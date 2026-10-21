# Atlas 交互改进计划

状态：第 1–5 期已于 2026-10-21 实施，见下方"实施记录"。涉及页面 `blueprint/lean_dependencies.html`；`dep_graph_document.html` 是同一个页面（`scripts/atlas_render.py:259`）。

## 已定

- 点击节点：在图右侧显示详情面板（窄屏时为底部抽屉），页面不滚动。
- 点击边：在新标签页打开 `atlas-audit.html` 中对应的行。
- 卡片墙：改成紧凑索引，另外生成一个完整卡片页 `atlas-cards.html`。

## 现状（实测）

用 headless Chromium 测量当前构建出的站点：

| | 桌面 1440×900 | 手机 390×844 |
|---|---|---|
| 页面总高度 | 144 屏 | 239 屏 |
| 在分支视图中点击节点 | 页面下跳 5.4 屏到对应卡片，图移出视野 | 下跳 7.1 屏，同样看不到图 |
| 在 unified graph 中点击节点 | 对话框关闭，页面跳到卡片 | 同左 |

此外：

- 点击边会离开当前页面，跳到 `atlas-audit.html`（930 KB）。
- 页面 HTML 共 3.2 MB：187 张卡片占 1.9 MB，12 个视图的 SVG 占 1.3 MB（其中 unified 一个就占约 0.7 MB）。MathJax 在加载时排版整页，约 7 秒后（含从 CDN 下载）才排完 2562 个公式。
- 相关代码：`site-src/assets/atlas.js:75` 的 `selectNode()` 先调用 `dialog.close()`（:84），再调用 `card.scrollIntoView()`（:88）；边的点击处理是 `location.assign(edge.dataset.audit)`（:235、:261）。

## 一、详情面板

默认 leanblueprint（`plastexdepgraph/templates/dep_graph.html`）的做法是：点击节点后弹出一个 `position: fixed`、宽 `90vw` 的浮层，显示陈述、"LaTeX" 链接和 Lean 声明链接，图留在原处。这比我们现在好，但浮层会遮住约 90% 的图，而 atlas 的价值恰恰在图上的边型对比和前驱/后继高亮。我们的卡片也比默认浮层长得多，需要一块能独立滚动的区域。因此用停靠在图旁边的面板：

```
桌面
┌ 分支导航 ┬────────── 图（平移 / 缩放）──────────┬────── 详情面板 ──────┐
│ 1. …     │                                      │ WZ2 Prop 6.3       × │
│ 2. …     │      ○ ──→ ●(选中) ──→ ○             │ Lean 状态 · 分支     │
│ …        │            ↑                         │ 陈述（MathJax）      │
│ Unified  │            ○                         │ Remark               │
│          │                                      │ 前驱 / 后继（按类）  │
│          │                                      │ ▸ Lean 版本          │
└──────────┴──────────────────────────────────────┴──────────────────────┘
窄屏（≤ 1000px，沿用 atlas.css 现有断点）：图在上方，面板为底部抽屉（约 55% 屏高，可展开）
```

- 选中节点只更新高亮和面板，`window.scrollY` 保持不变。面板打开时，`.atlas-content` 右侧留出面板宽度，图容器随之变窄但缩放比例不变。如果选中的节点不在可见区域，只平移图容器（`.diagram-scroll`），不滚动整页。
- 面板内容从上到下依次为：
  - 论文编号与标题、节点 ID、所属分支、Lean 状态；
  - 审阅后的手稿陈述，以及"在手稿中打开"链接（相当于默认浮层的 LaTeX 链接）；
  - 对应的 Remark；
  - 前驱和后继，按第二节的五类分组。例如"Lean 用到、路线图没有：…"和"路线图有、Lean 没用到：…"，点击条目即切换选中，每条边附带在新标签页打开见证的链接；
  - 折叠的 Lean 版本和专家原始表述；
  - "在 unified graph 中定位"。
- 前驱和后继直接从当前视图 SVG 的 `.depedge[data-from][data-to][data-kind]` 读取（`paintGraph()` 和 `applyEdgeFilters()` 已经在用这些属性）。
- 如果点到的节点不在当前视图里，就切换到包含它的视图：优先当前分支，其次第一个包含它的视图，最后才是 `all`。187 个节点中有 154 个出现在 `all` 以外的某个视图里，其余 33 个只在 `all` 中。
- Unified graph 用的是 `showModal()`，对话框外的元素都会变得不可交互。因此打开对话框时把面板元素移进 `<dialog>`（对话框内同样分成两栏），关闭时再移回原处；点击节点时不再关闭对话框。
- 键盘与无障碍：
  - Enter 选中节点（现已支持），Esc 关闭面板；
  - 面板打开时焦点移到面板标题，关闭后回到原来的节点；
  - 面板用 `<aside aria-labelledby=…>`。
- 地址：继续使用 `#node-ID`（`atlas-audit.html` 中有 1560 个这种链接）。页面加载或 hashchange 时直接打开面板并让节点居中。选中节点时用 `replaceState` 更新地址，不增加历史记录；关闭面板时清除 hash。
- 点击边：用 `window.open(edge.dataset.audit, '_blank', 'noopener')` 在新标签页打开（`atlas.js:235`、`:261`），同时在 `render_svg()` 里给边加 Graphviz 的 `target="_blank"`，让中键点击和无 JS 时行为一致。

## 二、边的差异：五类

现在实线只表示"Lean 有路径"，不管专家路线图有没有这条连接；虚线把"Lean 走了别的路"和"根本没法比较"混在一起。在 unified 视图中，299 条实线和 188 条虚线各自看起来完全一样。建议每条画出的边恰好属于下面一类：

| 类 | 含义 | 判定 | 建议样式 | unified 中现有数量 |
|---|---|---|---|---|
| A 一致 | Lean 有路径，专家路线图也有 | 两端都是专家节点，`kind=actual`，且在专家连接（242 条）的传递闭包中前驱可达后继 | 深色实线 | 72 |
| B 只有 Lean | Lean 有路径，专家路线图里连间接路径都没有 | 两端都是专家节点，`kind=actual`，闭包中不可达 | 醒目色加粗实线 | 13 |
| E Lean 细节 | 至少一端是专家图中没有的 Lean 版本节点，无从比较 | 任一端 `expert=false` | 细的浅灰实线 | 214 |
| C 只有专家（路线不同） | 两端的 Lean 版本都被根定理用到，但 Lean 里没有路径 | `kind=expert`，`classification=different-route` | 醒目色虚线 | 55 |
| D 只有专家（无法比较） | 一端没有对应声明、版本不在根定理闭包内，或两张卡共用一个声明 | `kind=expert`，`classification` 为 `unmapped`（76）、`outside-root`（54）或 `shared-declaration`（3） | 浅灰点线；unified 中默认隐藏 | 133 |

具体颜色在实现时确定：B 和 C 要醒目，且不能与选中节点（橙）、前驱（绿）、后继（蓝）的高亮色冲突；每类除颜色外还要靠线型或粗细区分，保证色盲读者也能分辨。

- 判定 A 和 B 必须用专家图的可达性，而不只是看有没有同一条直接边。72 条 A 中只有 25 条是专家画了同一条边，另外 47 条是专家经由更长路径连到的；只看直接边会把这 47 条误判成"只有 Lean"。
- 13 条 B 类边：
  - 12 条从定义或 API 节点出发：`W2DFrost`（WZ2 Def 7.3）3 条、`DFrost`（WZ1 Def 8.1）5 条，以及 `Igeom`、`W2DKT`、`W2TW`、`Dthin` 各 1 条；
  - 另 1 条是 `Ienvelope → W2Exists`。

  也就是说，Lean 的陈述用到了专家路线图没有连上的定义。在各分支视图中，每个视图的 B 类为 0–2 条。
- 显示方式：
  - 图例和开关按五类，每类显示数量；unified 默认隐藏 D，分支视图默认全部显示。
  - 悬停提示写明类别和原因。
  - 面板中按类分组列出前驱和后继（见第一节）。
  - 审计页新增一节，列出 B 类边，作为审阅清单。
- 实现：
  - `scripts/atlas.py`：在 `make_atlas()` 里对 `proposed` 计算一次专家图的传递闭包；`view_data()` 给每条边加一个 `diff` 字段。
  - `scripts/atlas_render.py` 的 `render_svg()`：边的 class 写成 `depedge <diff>`，并按类设置 style、color 和 tooltip。
  - `site-src/assets/atlas.css`：五类样式和图例。
  - `atlas.js`：把现有的两个复选框（`show-actual` / `show-expert`）换成五个。
  - `templates/atlas_audit.html`：新增 B 类清单。

## 三、Unified graph 收起与展开

用相同的 Graphviz 参数重新布局，估算各方案的画布面积（相对现在的 unified graph）：

| 方案 | 节点 | 边 | 画布面积 |
|---|---|---|---|
| 现在 | 187 | 487 | 100% |
| 只收起 external 框 | 132 | 410 | 65% |
| + 默认隐藏 D 类 | 132 | 278 | 51% |
| + 节点只显示粗体标题（摘要放进悬停提示和面板） | 132 | 278 | 32% |
| + 合并 11 对"陈述定义 + 证明它的定理" | 121 | 268 | 24% |
| + Graphviz `unflatten` 预处理 | 121 | 268 | 18–21% |

- external 框共 61 个节点，其中 53 个是 Lean 实现节点。各框分别为 cinematic 25、projection 15、multilinear 10、incidence 9、radial 1、extension 1；后两个只有一个节点，不需要收起。
- 合并规则：如果一个额外的 Lean 版本节点恰好是某个专家节点主证明的类型（例如 `FrostmanToKatzTaoWeightedCardStatement` 是 `W2L7_6` 主证明的类型），就把它并入那个节点。框外的 32 个额外版本里，有 11 个可以这样无歧义地合并。但合并会把"引用这个命题"和"引用它的证明"并到同一个节点，而 atlas 目前刻意区分这两者，所以建议默认不合并。
- 建议的默认状态：收起 external、隐藏 D 类、只显示紧凑标签。画布约为现在的 1/3，而且不改变任何证据的含义。"全部展开 + 显示全部五类"仍等于现在的 unified graph，可由工具栏按钮切换。
- 收起时：
  - 每个框画成一个节点，形状与普通节点不同，标签写框名和"N 个 Lean 节点"。
  - 进出框的边先按成员边判类，再按（起点, 终点, 类别）合并。合并后的一条边可能代表多条成员边，悬停提示和面板中列出这些成员边。
- 展开：点击框节点（或在其上按 Enter）就地展开，面板同时显示该框的说明、成员和进出边；展开后工具栏出现"收起"按钮。
- 展开的实现有两种方式：
  - (a) 服务端预渲染：生成 1 个收起版和 4 个"只展开一个框"的版本（radial 和 extension 只有一个节点，不收起），各存为单独的 SVG 文件，打开 unified graph 或点击展开时再加载。
    - 优点：沿用现有的 `render_svg()` 和 SVG 缓存，便于测试；页面也不再内嵌 0.7 MB 的 unified SVG。
    - 缺点：一次只能展开一个框（要看全部展开，可用 External 视图或"全部展开"版本）；展开时重新布局，其他节点会移动，没有过渡动画。
  - (b) 浏览器端布局：leanblueprint 已经把 d3-graphviz 拷进了站点的 `site/blueprint/js/`（`d3-graphviz.js` 80 KB、`hpcc.min.js` 117 KB、`graphvizlib.wasm` 1.1 MB、`d3.min.js` 248 KB），不需要新依赖。
    - 优点：任意组合展开，并有过渡动画，读者不容易丢失位置。
    - 缺点：要把 DOT 生成和 SVG 后处理（`atlas_render.py` 中给 SVG 元素加 id 和 data 属性的部分）移植到 JS；首次展开需要加载约 1.5 MB，并在浏览器中运行布局。
  - 建议先做 (a)，以后需要同时展开多个框时再换成 (b)。

## 四、下线 `lean_declarations.html`（建议，待确认）

- 它和 unified atlas 重复：
  - 它的 145 个声明全部是 unified atlas 中某个节点的主声明（145/145）；
  - 它的 280 条边在 unified atlas 中都有对应的实线路径（280/280）；
  - 两者的数据都来自 `lean-dependencies.json`。

  它独有的只是默认的 plastexdepgraph 浮层，以及用手稿标签命名节点。
- 做法：不再生成该页，只留一个跳转到 `lean_dependencies.html` 的小页面，以免外部的旧链接失效。
- 需要修改的位置：
  - 生成代码：`scripts/dependencies.py:457`，以及 `render_graph()`（:301）；
  - 测试：`tests/test_dependencies.py:118,150`；
  - 页面中的链接：`templates/lean_dependency_audit.html:27,33`、`templates/atlas.html:46`；
  - 文档：`README.md:271`。
- 前提：第三节的"全部展开"状态必须与现在的 unified graph 一致，这样下线后信息没有损失。

## 分期实施

1. **详情面板。**
   - `atlas.js`：
     - `selectNode()` 不再滚动，也不再关闭对话框，改为调用新的 `openPanel(key)`；
     - `openPanel()` 克隆已有的卡片，并去掉克隆体中所有 `id`（`openMap()` 克隆 SVG 时已有类似处理，见 :209）；如果 MathJax 尚未排完，就在 `MathJax.startup.promise` 之后对面板单独排版；
     - `openMap()` 在打开和关闭时移动面板；`readHash()` 改为打开面板；Esc 和"Clear selection"都会关闭面板。
   - `atlas.html`：加入面板骨架。
   - `atlas.css`：桌面 drawer，宽度 `clamp(360px, 34vw, 520px)`；≤ 1000px 时改为底部抽屉；打印时隐藏面板。
2. **边。** 点击边在新标签页打开见证；加入第二节的五类样式、开关、图例和审计页清单；面板中的前驱和后继按类分组。
3. **Unified graph。** 实现第三节的方案 (a)：收起 external，默认隐藏 D 类，只显示紧凑标签；unified SVG 改为按需加载。
4. **页面减重。**
   - 卡片改放进 `<template id="card-ID">`。加载时浏览器不会布局这些内容，MathJax 也不会排版它们；打开面板时只对这一张卡调用 `MathJax.typesetPromise([panel])`。
   - 卡片墙换成一个紧凑索引，列出 ID、论文编号、标题、分支和状态，支持搜索和筛选。`id="node-ID"` 放在索引行上，这样外部链接和锚点检查都继续有效。
   - 模板内不能再出现 `node-ID`。浏览器不会跳到 `<template>` 内的元素，但 `build.py` 用的 `HTMLParser` 不区分 `<template>`，会把其中的 id 也当作锚点，导致锚点缺失时检查仍误报通过。
   - 另外生成 `atlas-cards.html`，保留现在这种整页卡片，用于打印、无 JS 阅读和整页搜索。
5. **下线 `lean_declarations.html`**（见第四节）。

可选：章节页面上每条陈述的 "Uses" 弹窗显示的是 TeX `\uses`，它既不是专家图谱，也不是 Lean 导出的依赖。可以考虑改名或隐藏，免得读者把它和 atlas 中的依赖混淆。

## 验证

- 单元测试（`tests/test_atlas.py`）：
  - 五类判定，用合成图覆盖。其中"专家经由更长路径"应判为 A，"一端是额外 Lean 版本"应判为 E。
  - 收起后，按类统计的成员边总数与收起前相同；每个展开版本包含该框的全部成员；"全部展开 + 全部五类"与现在的 unified 边集完全相同。
  - 每个图节点恰好对应一张卡片和一行索引；模板内不出现 `id="node-…"`；`atlas-cards.html` 包含全部卡片。
- 浏览器冒烟测试：
  - 本机的临时环境 `/tmp/sticky-blueprint-venv` 里有 Playwright 1.64，`/usr/bin/chromium` 也可用；CI 没有安装这些。
  - 点击节点后 `scrollY` 不变，面板标题正确，节点没有被面板遮住。
  - 在 unified graph 中点击节点后，对话框仍然打开。
  - 点击边会打开新标签页（用 Playwright 的 `context.expect_page()` 检查）。
  - 点击收起的框节点会就地展开。
  - 打开 `#node-ID` 深链会直接打开面板；Esc 能关闭面板。
  - 在 390px 宽度下，底部抽屉出现，而且图仍在视野内。
- `python blueprint/scripts/build.py --reuse-docs` 通过，其中包括站点链接检查。

## 待定事项

1. 是否下线 `lean_declarations.html`（建议下线，保留跳转页）。
2. 是否把"陈述定义 + 证明"合并成一个节点（建议默认不合并）。
3. 展开的实现：先做服务端预渲染（建议），还是直接做浏览器端布局。
4. D 类虚线：只在 unified 中默认隐藏（建议），还是分支视图也默认隐藏。
5. 是否把浏览器测试加入 CI。

## 实施记录（2026-10-21）

已按建议实施第 1–5 期，与计划不同之处：

- 卡片不放进页面中的 `<template>`，而是只存一份在 `atlas-cards.html` 中，首次选中节点时由 atlas 读取。这样页面从 3.2 MB 降到 0.8 MB，也避免了站点产物逼近 GitHub Pages 1 GB 上限（第一版实现曾达到 999.1 MB）。
- `dep_graph_document.html` 也改为跳转页，不再是 atlas 的完整副本。
- 收起的框有 4 个（cinematic、incidence、multilinear、projection）；radial 和 extension 只有一个节点，不收起。
- 窄屏时如果选中的节点会被底部抽屉遮住，先平移图，不够时才滚动页面。
- 待定事项按建议处理：下线 `lean_declarations.html`；不合并"陈述定义 + 证明"；先用服务端预渲染；D 类只在 unified 中默认隐藏。浏览器测试暂未加入 CI。
