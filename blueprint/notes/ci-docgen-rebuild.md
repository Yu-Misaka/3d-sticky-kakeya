# CI 在没有改 Lean 时仍重建 doc-gen4

状态：2026-10-22 查明原因；2026-10-31 已在本仓库加入缓存复用修复。
下文的上游调查仍截至 2026-10-22。

## 现象

Blueprint workflow 有时只改了网页也要跑约 2.5 小时，正常约 10 分钟。根据 CI 日志汇总（用户 2026-10-22 提供的调查报告）：

| 提交 | 改了 `.lean` | 项目 Lean build | doc-gen4 build | 重建的 `docInfo` |
|---|---|---:|---:|---:|
| `8084c13` | 否 | 4.9 秒 | 96 分 | 9,062 |
| `8323a9d` | 否 | 5.2 秒 | 140 分 | 9,062 |
| `bcc8859` | 否 | 5.5 秒 | 6 秒 | 0 |
| `02839e3`（后被取消） | 否 | 4.7 秒 | — | 7,078 |
| `279a4cb` | 否 | 5.5 秒 | 6 秒 | 0 |
| `c0a0ca0` | 改了 `docbuild/Documentation.lean` | 5.0 秒 | 140 分 | 9,062 |

- 项目本身的 Lean 编译每次都由缓存直接重放。
- GitHub Actions 缓存每次都恢复成功：`02839e3` 和 `bcc8859` 恢复的是同一份 `279a4cb` 缓存，一慢一快。
- 慢的运行里，`docs.py` 都打印了 "Reusing doc-gen4 data"。随后 Lake 重建 `UnicodeBasic/UnicodeCLib`、`doc-gen4:exe`、coreDocs、全部 `docInfo` 和 HTML。

## 原因

1. doc-gen4 依赖 UnicodeBasic（本仓库锁定的是 `fgdorais/lean4-unicode-basic@3b87338`）。它的 `lakefile.lean` 第 15–25 行用 `readDir` 列出 `UnicodeCLib/` 里的 4 个 C 文件，没有排序，就按这个顺序把对象交给 `buildStaticLib`。
2. Lake 的 `buildStaticLib` 用 `Job.collectArray` 按数组顺序合并输入 trace。对象内容完全相同、只是顺序不同，静态库的输入 hash 也会变。
3. 静态库重建后，`doc-gen4:exe` 随之重建。而 coreDocs、每个模块的 `docInfo` 和 HTML 都依赖这个可执行文件，于是包括 Mathlib 在内的全部文档数据重建。
4. 目录的枚举顺序由文件系统决定。在 ext4 上，这个顺序取决于文件名的哈希，哈希种子每个文件系统各不相同，所以同样的检出在不同 runner 上可以得到不同顺序。这能解释为什么同一份缓存一次慢一次快。不过历史日志没有记录当时的枚举顺序，这一步是推断。
5. 修复前，本仓库的 `blueprint/scripts/docs.py` 也没有挡住：`prepare_docs()` 判定指纹一致后只是保留数据，`build_docs()` 随后仍无条件运行 `lake --no-cache -d docbuild build Documentation:docs`。

本机验证（Lean 4.32.0-rc1，Linux）：
- 全新 clone 加上恢复的 `.lake`，项目模块和 doc-gen4 都报 "All targets up-to-date"。
- 只把 UnicodeCLib 的对象顺序改为排序后的顺序，C 源码不变，Lake 就报 `UnicodeBasic/UnicodeCLib` 过期，需要重建。

另一项独立的成本：只要 Lean 输入（源码、toolchain、manifest、`Documentation.lean`）有任何变化，`prepare_docs()` 就会清空全部文档数据。所以改 Lean 的提交总要付一次约 2.5 小时，这是现有设计（`c0a0ca0` 慢就是这个原因）。

## 上游状态（2026-10-22）

- UnicodeBasic 的 main（`5e46d45`）、全部 15 个分支和 189 个 PR，都没有在 `readDir` 之后排序。
- doc-gen4 最新（`0656b7e`，v4.36.0-rc1）仍依赖 UnicodeBasic，锁定的 `a24bcde` 同样未排序。
- Lean v4.35.0 的 `buildStaticLib` 与 v4.32.0-rc1 相同，`readDir` 仍直接返回操作系统给出的顺序。
- 在三个仓库按标题检索（readDir、UnicodeCLib、sort、order、rebuild、deterministic）没有找到相关的 issue 或 PR。检索时 API 被限流，只搜了网页上的标题。

## 本仓库修复（2026-10-31）

1. `prepare_docs()` 返回是否需要重建。输入指纹与 stamp 一致且
   `cache_complete()` 时，`build_docs()` 不启动 Lake，只运行 `finish_docs()`，
   检查文档模块和声明链接，并把源码链接刷新到当前提交。缺失、损坏或过期的
   stamp，以及不完整的缓存，仍走重建流程。
2. CI 将 Lean 编译与审计、doc-gen4、站点生成拆成独立步骤。文档验证成功后，
   立即通过 `actions/cache/save` 保存缓存，再执行 PDF/HTML 检查。这样 PDF
   排版错误不会导致前面几个小时的文档构建成果丢失。文档阶段失败时不保存缓存。
3. 缓存 key 使用 `docs.py fingerprint` 输出的输入指纹，与文档 stamp 相同。
   只改网页或 TeX 时命中同一份缓存，不再按每个 commit 上传重复快照。
   保留兼容依赖的旧 `blueprint-v2` key 作为恢复后备，避免迁移时丢弃已有缓存。
4. 回归测试覆盖缓存命中时不调用 Lake、输入变化或缓存缺失时重建、失败构建
   不写成功 stamp，以及复用时仍验证文档并刷新源码链接。输入指纹测试确认
   网页/TeX 修改保持 key，而 Lean、toolchain、manifest 和文档入口修改改变 key。

首次构建、缓存被清理或 Lean 输入变化仍可能耗时较长；全量文档失效策略
保持不变。此修复消除的是输入未变化时的无效重建，以及 PDF/HTML 失败导致的
重复重建。

## 上游修复建议

UnicodeBasic 仍可通过排序消除目录枚举顺序对静态库 trace 的影响：

```lean
for file in (← (pkg.dir / "UnicodeCLib").readDir).qsort (·.fileName < ·.fileName) do
```

合并后还要等 doc-gen4 更新锁定的版本。本仓库的复用修复不依赖该上游变更。
