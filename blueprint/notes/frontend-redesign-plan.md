# Blueprint 前端重做方案

状态：Home、Atlas、Manuscript 和 Evidence 已于 2026-10-22 上线，原型和 `/preview/` 已删除（原型源码见提交 `8323a9d`）。与方案不同之处见文末"实施记录"。

## 现在用着不舒服的地方

在 headless Chromium 中实测当前构建出的站点：

| | 桌面 1440×900 | 手机 390×844 |
|---|---|---|
| 打开 atlas 时图的位置 | 从 y = 633 开始，只露出 267 px（三成屏高） | 在 1.7 屏以下，看不到 |
| 打开面板后图的宽度 | 625 px（43% 屏宽） | 底部抽屉占 464 px |
| 页面总高度 | 12 屏 | 26 屏 |

具体问题：

- **图不是主角。** 深蓝 header、"Scope" 折叠块和两行边类复选框都排在图前面；下面还有 187 行的节点索引，整页可以滚动，图容器内部也能滚动，形成两层滚动。
- **手势不一致。** 分支视图要按 Ctrl + 滚轮才缩放，unified graph 直接滚轮缩放；"Fit width"、"Readable size" 和缩放百分比各视图分开记。
- **两种模式。** Unified graph 是 `showModal()` 对话框，详情面板要在页面和对话框之间搬来搬去；展开一个框时换一张重新布局的 SVG，没有过渡，读者会丢失位置。
- **面板的顺序。** 前驱和后继排在卡片最底部，而它们恰恰是导航最需要的；点边的"witness"会在新标签页打开 948 KB 的审计页。
- **节点。** Graphviz 原生椭圆和方框加三行文字，其中一整行是"Lean proof · used"这种状态文字；颜色写在 SVG 的内联属性里，CSS 无法统一主题，也做不了暗色模式。
- **全站四套视觉语言。** 首页是米色加衬线；atlas 和 atlas-audit 是深蓝 header 加 system-ui；手稿是 plasTeX 默认主题，带它自己的侧栏；`lean_dependency_audit.html` 又是另一套。页面之间的导航也不一致：手稿里回到 atlas 的唯一入口是目录中的"Dependency graph"，它经过一个跳转页；定理旁的"Uses"弹窗显示的是 TeX 的 `\uses`，容易和 atlas 的依赖混淆。

## 原则

1. **图是主角。** Atlas 做成占满窗口的应用，整页不滚动。
2. **一块画布、一套手势。** 分支视图和整体图是同一块画布上的不同视图，不再用对话框。
3. **先导航，后细节。** 检视面板先列连接，再给陈述、Remark 和 Lean 版本。
4. **证据就地显示。** 点边时在面板里显示见证路径，不离开页面。审计页保留，作为完整表格。
5. **全站一套设计。** 同一个顶栏，同一组字体和颜色 token，亮色和暗色两套主题。
6. **不增加体积，不引入框架。** 按 `build.py` 的估算方式，Pages 产物现在是 995.9 MB，距 1 GB 上限只剩约 4 MB。

## 信息架构

全站顶栏：`Sticky Kakeya | Home · Atlas · Manuscript · Evidence · Lean docs ↗ · PDF ↗ | 搜索 ⌘K`

- **Home**：定理陈述（MathJax）、三个入口，以及两组真实计数：102 个路线图节点的 Lean 状态，整体图 487 条边的五类分布。作者和单位保留。
- **Atlas**：见下一节。
- **Manuscript**：plasTeX 输出换皮。统一顶栏，左侧章节目录，正文宽约 68 个字符，用衬线字体。每个定理标题行右侧有"Lean · N"（展开声明列表）和"Atlas"（跳到对应节点）两个徽章；证明默认折叠。
- **Evidence**：`atlas-audit.html` 和 `lean_dependency_audit.html` 合并为一页，分 Connections 和 Versions 两个标签，共用表格样式、筛选和粘性表头，Lean-only 清单放在最前面。
- **Lean docs**：doc-gen4 不改，只从顶栏链接。
- **`atlas-cards.html`**：保留，用于打印和无 JS 阅读，换成新样式。

## Atlas

```
Desktop
+- site bar: Home | Atlas | Manuscript | Evidence | Lean docs | PDF ------------ [ Search  Cmd-K ] -+
| Views         | Core proof DAG                          - 78% + Fit | < >  1/3        Link    |
|  1 Core DAG   | (description, 2 lines)                              | GRAINS . WZ2               |
|  2 Wolff ...  |                                                     | WZ2 Proposition 6.3        |
|  ...          |        [node] ---> [selected] ---> [node]           | Used Lean proof  W2P6_3    |
| 11 External   |                                                     | Depends on 3 / Used by 2   |
|               | +- Lean vs roadmap -+                               | Statement (MathJax)        |
| Whole proof   | | agree        24   |                   +- map -+   | Correspondence remark      |
|               | | lean only     0   |                   |       |   | Lean versions (folded)     |
+---------------+-+-------------------+-------------------+-------+---+----------------------------+
Phone: site bar + view menu; full-screen canvas; details as a bottom sheet (peek / half / full)
```

### 画布

- **手势**：拖动平移，触控板双指滚动也平移；Ctrl/⌘ + 滚轮或双指捏合缩放；键盘 `+` `−` `0`；所有视图一致。
- **语义缩放**：缩放到 72% 以下时节点只显示粗体的论文编号，30% 以下时只剩分支颜色的色块，整张图像一张按分支着色的地图；放大后显示摘要。这取代现在单独生成的 compact 变体。Whole proof 打开时先显示全图。
- **小地图**：节点超过 40 个的视图（External、Whole proof）在右下角显示小地图，可点击或拖动定位。
- **选中**：选中节点用强调色描边；相邻节点和边保持原样并加粗，其余淡出。不再用绿色和蓝色区分前驱和后继，因为方向已经由布局（结论在上）和箭头表示，颜色留给五类边。
- **折叠框**（Whole proof）：点框节点即展开。展开前后的两个布局都是构建时算好的，节点按 id 对齐后做位置插值动画，成员节点从框节点的位置散开，边随后淡入，相机随之移到展开后的框。
- **图例就是开关**：左下角列出五类边和当前视图中的数量；点击显示或隐藏该类，悬停时只突出该类。Whole proof 默认隐藏"not comparable"，与现在相同。
- 背景是随画布平移和缩放的点阵网格，方便判断移动的距离。

### 节点

- 统一用圆角矩形，文字更紧凑。浅底色表示分支，右上角的符号表示 Lean 状态：形状表示角色（● 证明、◆ 命题接口、■ 定义或数据、▲ 构造子），实心表示根定理用到，空心表示在根定理闭包之外；没有 Lean 对应的节点用虚线边框。状态文字移到悬停提示和面板中。
- 现在"椭圆 = 证明值"的形状编码改由符号承担。

### 检视面板

- **节点**：
  - 标题区：分支 · 来源 · 页码，论文编号（大号衬线），标题，状态，可复制的 ID，← → 浏览历史；
  - 连接：分"Depends on"和"Used by"两组，各按五类分组；悬停时在图上突出，点击即切换选中，"evidence"在面板内打开该边；
  - "Appears in"：列出包含它的视图，点击即切换；
  - 审阅后的手稿陈述，附"在手稿中阅读"链接；
  - Correspondence Remark；
  - Lean 版本：默认只显示短名、角色和是否用到，展开后显示完整类型、doc-gen4 和源码链接，以及从根定理到它的引用路径；
  - 专家原始表述，默认折叠。
- **边**：两端（可点击）、类别和一句解释、判定原因，以及逐步的内核见证：声明 → 引用种类 → 声明，每个声明都链接到 doc-gen4。折叠边列出它代表的每条成员边。
- **未选中时**：显示当前视图的说明和本视图的节点列表（结论在前）。

### 搜索

`⌘K` 或 `/` 打开，可按论文编号、ID、标题和 Lean 声明名搜索。回车后跳到包含该节点的视图，依次优先当前视图、第一个包含它的分支视图、Whole proof（必要时打开对应的框）。它取代页面底部的 187 行索引。

### 地址

继续使用 `#node-ID`（审计页中有 1560 个这种链接）。

## 技术方案

- **布局 JSON 代替 SVG。** 布局仍在构建时由 Graphviz 计算，结果确定，也便于测试；但改为输出 `dot -Tjson`，再压缩成布局 JSON（节点框、边的贝塞尔路径、框的外框），由浏览器用 JS 画成 SVG。样式全部通过 CSS class 和 token 控制。
  - 好处：主题、暗色模式、选中态、语义缩放和过渡动画都由 CSS/JS 控制；`render_svg()` 中给 Graphviz SVG 补 id 和 data 属性的后处理可以删掉。
  - 体积（原型实测）：11 个分支视图加 6 个整体图变体共 17 个布局，合计 0.60 MB JSON。它替代 `lean_dependencies.html` 中内嵌的 SVG（页面共 0.84 MB）和 6 个 `atlas-unified-*.svg`（共 3.7 MB）。
- **节点数据一次加载。** 原型的 `atlas.json` 为 1.07 MB，包含陈述 HTML、Lean 类型和见证路径，atlas 不再解析 `atlas-cards.html`。现有的 `atlas-dependencies.json`（1.5 MB）与它大部分重叠，可以考虑合并成一个文件。
- **不引入框架，也不加构建步骤。** 用原生 JS（ES 模块），静态页继续用 Jinja 模板。
- **字体**：陈述和标题用 STIX Two Text，界面用 IBM Plex Sans，Lean 名用 IBM Plex Mono。可以自托管 woff2 子集（约 200 KB），也可以用 Google Fonts。
- **手稿换皮**有两种做法：
  - 用 plasTeX 的 `extra-css` / `extra-js` 选项，加一个小脚本注入顶栏和定理徽章；
  - 在 `build.py` 中对 `web/` 的输出做一次 Python 后处理，更便于测试，建议用这种。
- **MathJax**：继续从 CDN 加载 v3，atlas 只对当前打开的面板排版。

## 分期

1. 设计 token、全站顶栏、Home。
2. Atlas 外壳和画布：布局 JSON、手势、语义缩放、小地图、图例开关；替换分支视图。
3. 检视面板（节点和边）、搜索、Whole proof 的折叠动画；去掉对话框。
4. 手稿换皮和定理徽章。
5. Evidence 合并，`atlas-cards.html` 换样式。测试方面：单元测试检查布局 JSON 的边集与现有边集一致；Playwright 冒烟测试，是否加入 CI 待定。

## 原型

- 数据来自当前构建：`atlas-dependencies.json`、`atlas-cards.html` 和 `chap-sticky.html`。布局用本机的 Graphviz 2.43 按新的节点尺寸重新计算，见 `blueprint/prototype/prep.py`。
- doc-gen4、源码和手稿中的链接指向线上站点。
- 原型包含 Home、Atlas 和 Manuscript（只有第 3 章）三个页面；Evidence 页、打印页和完整的无障碍检查没有做。

## 待定事项

1. 鼠标滚轮：用来平移（Figma、tldraw 的习惯，对触控板友好），还是用来缩放（地图的习惯，也是现在 unified graph 的行为）？原型用的是平移，Ctrl/⌘ + 滚轮缩放。
2. 是否取消"椭圆 = 证明"的形状编码，改用状态符号？
3. 是否取消前驱绿、后继蓝，改靠方向和面板区分？
4. 手稿换皮做到什么程度：只加顶栏和徽章，还是整套换主题？
5. 定理旁的"Uses"（TeX `\uses`）弹窗：改名还是隐藏？
6. 字体自托管还是用 Google Fonts？
7. 两个审计页是否合并？

## 实施记录（2026-10-22）

- **Atlas**（`lean_dependencies.html`）：按原型实现。
  - `scripts/atlas_render.py` 的 `layout_view()` 用 `dot -Tjson` 布局，缓存在 `build/atlas-layout/`。
  - `page_data()` 把卡片、17 个布局、每条边的比较记录和见证路径写进 `atlas-view.json`（1.64 MB，见证路径去重后存成一张表），页面本身 36 KB。
  - 页面脚本是 `site-src/assets/atlas.js`。6 个 `atlas-unified-*.svg` 和 `render_svg()` 已删除。
  - 原型里见证链的声明链接到 doc-gen4，但链上有 private helper，doc-gen4 没有它们的页面，因此改为链接到源码。
  - 数据里的链接（陈述、Remark、doc-gen4、审计页锚点）在 `build.py` 的站点链接检查中一并检查。
- **Evidence**（`atlas-audit.html`，948 KB → 287 KB）：
  - 删去"每条画出的箭头"一节，这部分改由检视面板显示。
  - 保留：Lean only 清单、242 条路线图连接（可按分类筛选和搜索）、方法说明和来源指纹。
  - Lean only 清单从整体图的 13 条改为所有视图的 17 条，其中 4 条只出现在分支视图里。
  - "有 Lean 路径但没有单独箭头"的 5 条连接带有标记。
  - 行锚点改为 `#connection-FROM-TO` 和 `#lean-only-FROM-TO`；专家把两对连接各记录了两次，第二条加 `-2`。旧的 `#edge-<hash>` 锚点不再存在。
- **`lean_dependency_audit.html`**（1.57 MB → 1.1 MB）：换成新样式，删去"Inspect the paths behind graph edges"一节。这些见证在 atlas 和 `lean-dependencies.json` 中都有。
- **Manuscript**：`scripts/manuscript.py` 在 atlas 读完 plasTeX 的陈述之后转换 15 个 plasTeX 页面。
  - 页面套上统一顶栏，左侧是章节目录，正文保留 plasTeX 生成的全部内容和锚点。
  - 定理标题旁的图标换成"Lean · N""Uses · N""Atlas →"三个徽章。徽章用 `<details>` 实现，没有 JS 也能用。
  - 证明折叠成 `<details>`；页首有"Open all proofs"，链接指向某个证明时自动展开。
  - leanblueprint 主题的 `js/`、`styles/`、`symbol-defs.svg` 和 `src/extra_styles.css` 已删除。
  - 新增依赖 `beautifulsoup4==4.12.3`。
- **Home**：由 `templates/home.html` 在构建 atlas 时生成。定理陈述取自手稿，计数取自 atlas；`site-src/index.html` 和 `site.css` 已删除。
- **样式**：
  - `assets/theme.css`：颜色和字体 token、顶栏、状态标记和边类色样。
  - `assets/atlas.css`：atlas 页面。
  - `assets/pages.css`：首页、手稿、证据页和卡片页。
  - 字体暂用 Google Fonts。
- **体积**：Pages 产物按 `build.py` 的估算从 995.9 MB 降到 989.8 MB。
- **待定事项**：1–3 按原型的做法实现；5 保留"Uses"这个名字，弹出列表注明这是手稿里的引用，不是 Lean 依赖；6 暂用 Google Fonts，7 已按上面的方式精简，两页没有合并。浏览器测试仍未加入 CI。
- **2026-10-22 修正**：
  - 检视面板的公式在线上不渲染。原因：MathJax 比 1.6 MB 的 `atlas-view.json` 先就绪时，就绪钩子已经执行过，之后的排版请求只会排队。现在 `atlas.js` 启动时会先检查 MathJax 是否已就绪。
  - 面板宽度可拖动左边缘调整（300 px 至窗口的 62%，并给画布至少留 520 px），双击恢复默认，宽度保存在 localStorage。拖动时图不移动，因为画布原点在左边。
  - 面板变窄时有两处版面问题：
    - MathJax 3 不会把行内公式折行。放不下的行内公式现在单独占一行并可以横向滚动（`.mjx-wide`），面板尺寸变化时重新判断。这也修好了默认宽度下原有的溢出：例如 1280 宽的窗口里，`T5_2` 的一条公式也会超出。
    - 连接列表里过长的标题现在可以换行。
  - 画布上的浮层按画布自身的宽度调整（container query），不再按窗口宽度。
  - 对 187 张卡片在 300 px、340 px、684 px（最大）以及 1100 px 宽窗口下逐一检查，均没有可见内容溢出，画布浮层互不重叠。
- CI 有时重建全部 doc-gen4 文档的原因记录在 `ci-docgen-rebuild.md`。
