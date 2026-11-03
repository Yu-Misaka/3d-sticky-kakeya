这份中文说明逐一讨论 Core proof DAG 的 18 个节点，展开当前 Lean 声明的数学内容，并说明它们与 Roadmap 或打印论文之间的区别。第 10 节逐条解释 Roadmap 的 17 条连线，第 11 节解释 Lean 在 Core 中另画出的 5 对端点。两张图共用节点位置。

- 正文：[core-proof-dag-lean-roadmap.tex](core-proof-dag-lean-roadmap.tex)
- 编译后的 PDF：[core-proof-dag-lean-roadmap.pdf](../print/core-dag/core-proof-dag-lean-roadmap.pdf)
- 节点、编译类型和全部引用路径：[core-proof-dag-evidence.json](core-proof-dag-evidence.json)
- 对照图的 TikZ 源码：[core-proof-dag-figures.tex](core-proof-dag-figures.tex)
- 给 Seed Evolving 的全文讲解及复述问题：[core-proof-dag-seed-evolving-task.md](core-proof-dag-seed-evolving-task.md)
- Seed Evolving 的源码核对和复述：[core-proof-dag-seed-evolving-review.md](core-proof-dag-seed-evolving-review.md)

在仓库根目录重新生成证据与图：

```bash
python3 blueprint/notes/core-proof-dag-evidence.py
```

编译需要 XeLaTeX、ctex、Noto CJK 字体和 Graphviz。编译命令在 `blueprint/notes` 中运行：

```bash
latexmk -xelatex -interaction=nonstopmode -halt-on-error \
  -outdir=../print/core-dag core-proof-dag-lean-roadmap.tex
```

PDF 与编译日志按仓库现有约定放在忽略的 `blueprint/print` 和 `blueprint/build` 内。正文、TikZ、JSON、再生成脚本和交接记录保留在 `blueprint/notes` 中。
