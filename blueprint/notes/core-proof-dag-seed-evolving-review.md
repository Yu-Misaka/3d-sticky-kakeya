# Seed Evolving 对 Core proof DAG 主稿的复述与审查

## 核查范围

我已完整阅读 `core-proof-dag-seed-evolving-task.md`、`core-proof-dag-lean-roadmap.tex` 和 `core-proof-dag-evidence.json`，并按证据中的声明位置回到 Lean 源码核对。本文只写入 review；未修改主文稿或 Lean 文件。

本次没有重新运行 LaTeX 或全量 Lean build，也没有重新生成证据 JSON；以下结论来自当前工作树的静态源码、已有编译依赖 JSON 和关键声明本体核对。

总体结论：主稿对 18 个节点、17 条 Roadmap 线和 17 条 Lean 线的关系把握是准确的。最重要的几处边界也说清楚了：Lemma 2.13 没有独立主声明；完整 WZ1 二择一接口不在根闭包；Lemma 6.6 的实际使用版本带归一化质量和重数条件；Proposition 7.1 改的是长度 32 的粗测试；最终上下界作用在同一个终端族、shading 和斜率上。未发现会推翻主线论证的数学错误，但有若干句容易让读者把“兼容 API”误读成“根证明路线”，建议修订。

## 原 Lean 源码核对

以下核对均直接查看声明本体，而不是只看 atlas remark。

1. `MyLeanRepo/Kakeya/Assouad/PropStickyDefinition2_12.lean:703`：`WZ2PaperPureCWAAtNearbyScales` 是命题；其中实际尺度满足 `rho₀ ≤ rho` 且 `rho < C * rho₀`，并要求普通论文意义的本质不同和完整附近尺度覆盖。它没有额外写 `rho ≤ 1`。

2. `MyLeanRepo/Kakeya/Assouad/PropStickyDefinition2_12Extremal.lean:41`：`WZ2PaperPureIsExtremal` 是结构命题，字段包括非空、nearby-scale CWA、总体 shading 密度和 `volume shading.union ≤ δ^(sigma-loss)`；它不是存在性定理。

3. `MyLeanRepo/Kakeya/Assouad/PureWZ2/LargeSlope/Section6ScaleData.lean:20`：准备 slab 数据明确保存同族 whole-cell subshading、质量下界、覆盖数和细重数上界。质量项是 `δ^(loss+2) * family.enncard * scale`，不是单纯的 `δ^loss * scale`。

4. `MyLeanRepo/Kakeya/Assouad/PureWZ2/LargeSlope/Lemma66PreparedInterval.lean:18` 和 `:190`：准备版 Lemma 6.6 接收配置、归一化斜率、slab scale data、框架相容性和额外重数条件；在 `sqrt δ ≤ r ≤ δ^ε` 下给导数下界。

5. `MyLeanRepo/Kakeya/Assouad/PureWZ2/LargeSlope/Lemma66NormalizedInterval.lean:20`：任意给定配置版本不重新选择 C² 配置，也不要求全局框架前提，但仍明确要求 `π/4 * δ^(η/16+2) * #T * r` 的质量、slab 覆盖和细重数上界。

6. `MyLeanRepo/Kakeya/Assouad/WZ1/Statements.lean:1105`：完整 `WZ1ProjectionDichotomyConclusion` 只是 `def ... : Prop`。集中分支要求 F 在过原点的 `v⊥` 线附近，而 G1、G2 各自在同一条仿射线 `b + R v` 附近；投影分支量化到所有足够大的三元关系 H。

7. `MyLeanRepo/Kakeya/Assouad/WZ1/ProjectionTheoremFinalStatements.lean:85`：实际使用的 union 结论要求标准分离、相对 Frostman 计数和均匀三重密度；集中分支只要求 G1 或 G2 中一个端点类有足够直线计数。

8. `MyLeanRepo/Kakeya/Assouad/WZ1/WellSeparatedProjectionUnion.lean:45` 与 `MyLeanRepo/Kakeya/Assouad/OSWInput.lean:26`：`wz1_well_separated_projection_union` 是已证明 theorem，末尾使用的 `osw_input` 本身也是由 `radial_bootstrapping_measure_thin_tubes` 闭合的 theorem，不是留给最终定理调用者的 proof 参数。

9. `MyLeanRepo/Kakeya/Assouad/PureWZ2/SlopeOffsetGeometry.lean:20`、`:38`、`:68` 和 `:215`：`k = 1/(4(1+|s|))`，三维仿射变换为 `(k(x+sy), ky, z)`，三维行列式是 `k²`；扭曲投影到二维后的面积倍数是 `k`。

10. `MyLeanRepo/Kakeya/Assouad/PureWZ2/PaperTerminalNormalization.lean:19`：归一化终端保存源指标单射、轴线像、shading 包含关系和 `analysisSlope = f.centered`，因此最终终端与 Proposition 6.5 的实际输出有可追踪关系，不是另选一份对象。

11. `MyLeanRepo/Kakeya/Assouad/PureWZ2/DilatedTubeWolff.lean:20`：长度 32 的 `DilatedTubeWolffVolumeBound` 只改变粗测试胶囊；细管族不变。`:119` 的参数 Frostman 推导显式给出常数 `128000 = 320 * 20²`。

12. `MyLeanRepo/Kakeya/Assouad/PureWZ2/DilatedTubeWolffLowerBound.lean:25`：选中的 Proposition 7.1 仍有 `#F ≤ δ^{-cardExponent}` 前提；`:82` 的竖直图入口用本质不同和有界性 packing 后取指数 7；`:132` 的 CWA 入口再把长度 32 粗测试由凸性提供。

13. `MyLeanRepo/Kakeya/Assouad/PureWZ2/NormalizedContradiction.lean:23`：证明先调用独立下界取得 `eta, delta₀`，再让 upper producer 返回 `data`；下界应用到 `data.family`、`data.shading`、`data.analysisSlope` 及其证书，并与 `data.projection_upper` 比较。

14. `MyLeanRepo/Kakeya/Assouad/TwistedProjectionScale/ParameterBlockRepresentativeCinematicStatements.lean:24`、`MyLeanRepo/Kakeya/Cinematic/WZ2UniformC2Input.lean:26`、`MyLeanRepo/Kakeya/Assouad/TwistedProjectionScale/SignedWindowSharpDensity.lean:17`：分别核对了代表块 cinematic 回传、cinematic 常数量词顺序，以及 Lemma 7.12 从输入 `δ^η` 密度到输出 `δ^(4η)` subshading 的陈述。

15. 两种本质不同也已核对：`PropStickyDefinition2_12.lean:286` 的论文定义是双方都不在对方中心 2 倍放大中；`MyLeanRepo/Kakeya/AssertionD.lean:71` 的分析定义是交集体积不超过较大管体积的一半。`OrdinaryDistinctToOverlapDistinct.lean:618` 在 `δ ≤ 1/100000` 下从前者推出后者，但不是无条件等价声明。

16. 方位差异已核对：`blueprint/src/chapters/smooth-grains.tex:99` 的 remark 指出打印卡中 F/G 方位与点积差所需方位相反；Lean 的 `Statements.lean:1122-1132` 确实把 F 放在过原点的 `v⊥` 线、把 G1/G2 放在仿射线。

## 12 个问题的逐条复述

### 1. 为什么 P6.4 到 L6.6 没有所选主声明依赖，而二者分别进入 P6.5

`pure_wz2_left_line_c2_grains` 是一个生产者：给定正临界 package 和损失、尺度上限，它实际选择并返回一份 C² grains 配置。准备版 Lemma 6.6 则是条件引理：它的参数中已经有一个 `PureWZ2C2GrainConfiguration`、一个区间和 slab 准备数据；它证明“如果这份给定数据满足质量、覆盖、重数和框架条件，则导数有下界”。

因此，Lemma 6.6 的类型会提到 C² configuration，但它的证明不需要调用 P6.4 再构造一份配置。类型依赖和证明依赖必须分开。P6.5 的实际构造一方面调用 P6.4 取得共同来源，另一方面在选出 slab 并组装准备数据后调用 Lemma 6.6。证据路径也正是 `W2P6_4 → W2P6_5` 直接相连，而 `W2L6_6 → W2P6_5` 经七步编译引用相连；没有 `W2P6_4 → W2L6_6` 的主声明路径。

### 2. Sigma 到 D6.1 为什么缺线

Lean 的 `PureWZ2Admissible sigma` 是关于显式实数 `sigma` 的谓词：在任意损失和任意尺度上限下，都能找到更小尺度的反例配置。临界提取证明在最终定理失败时局部选取一个 `0 < sigma < 1` 的 package，但没有导出一个全局名为 `sigma_CW` 的常数。

`WZ2PaperPureIsExtremal sigma loss delta family shading` 同样把 `sigma` 作为显式输入。定义一个极端配置结构时，只需要把调用者给的 `sigma` 写进类型，不需要引用“这个 `sigma` 是 admissible”的谓词，更不需要重新取上确界。后来临界 package 负责把局部选出的指数传入。因此两个主声明都被根证明使用，但 D6.1 定义到 Sigma 谓词没有依赖路径。

### 3. Lemma 2.13 的无独立对应与特定覆盖证书有何不同

Roadmap 的 Lemma 2.13 是一般继承命题：从每尺度 CWA 出发，在附近尺度选择覆盖，并使粗族和完整重缩放纤维继续满足多尺度性质。当前映射中该节点没有 primary，也没有独立 Lean theorem。

实际 P6.2 及后续结构会为自己使用的具体尺度、父管、完整纤维和 re-entry 数据重建证书。这些证书足以支持当前构造函数的输入输出，但它们是在特定运行数据和结构约束下建立的，不能外推出“任意精化都满足一般继承引理”。所以两条接在 Lemma 2.13 上的 Roadmap 线被标为 `unmapped`，不是提取器漏掉同名调用。

### 4. 完整 WZ1 二择一接口与实际 C2 使用结果

完整接口处理三个非空、`δ`-分离且位于单位球的有限点集 F、G1、G2。三者均满足维数 1 的绝对 Katz-Tao 上界，即球内点数按 `(r/δ)` 增长并有 `δ^-η` 损失。

第一个分支中存在单位方向 v 和基点 b，使 F 在过原点的方向 `v⊥` 直线附近至少有 `δ^(ε-1)` 个点，同时 G1 和 G2 各自在同一条仿射线 `b + R v` 附近有这么多点。第二个分支对每一个足够大的三元关系 H，即 `#H ≥ δ^(η-3)`，给一个尺度 `ρ` 和一段长度至少 `δ^-η ρ` 的截线，使点积差集合 `a·(b1-b2)` 的 `ρ`-覆盖数达到 `(长度/ρ)^(1-ε)`。

实际 C² 构造调用的不是这个完整接口，而是 `wz1_well_separated_projection_union`。该结果要求三点类已经标准分离，满足相对 Frostman 计数，并只处理一份均匀三重稠密的 H；集中分支只要求 G1 或 G2 中一个端点类出现直线集中。当前应用里两个端点类来自同一个局部环境集合 G 的精化，所以把任一端点类的集中传回 G 就足够。这个结果范围更具体、集中分支更弱，但条件由 C² 构造实际准备好，因而足以支持当前路线。

方位差异也不能忽略。若端点 `b1,b2` 沿方向 v 排列，则 `b1-b2 ∥ v`，能使 `a·(b1-b2)` 退化的系数 a 位于过原点的 `v⊥`。所以点积差模型中 F 靠过原点的正交线、G 靠仿射线；这与打印卡把 F 放在仿射线、G 放在过原点线的叙述相反。例子 `F={0}×[1/2,3/4]`、`G=[1/2,3/4]×{1}` 中所有 b 差都是水平向量，而 F 中 a 是竖直向量，故点积差恒为零；同时 G 明显不近过原点的水平线。

### 5. Lemma 6.6 的绝对质量与归一化质量差别

打印图卡的 slab 质量是绝对形式：

```text
Σ_i |Y_i ∩ (R² × J)| ≥ δ^η |J|.
```

准备版使用的是同族 whole-cell subshading `Y_J`，其质量至少为

```text
(π/4) δ^(η/8+2) #T |J|.
```

同时还要求 slab 并集覆盖数、两类重数上界和框架相容性。新的任意给定配置版本把预算改为 `2000η ≤ εσ²`，接受外部给定的 C² 配置和区间 J，内部构造 whole-cell hull 与框架证书，但质量仍是

```text
(π/4) δ^(η/16+2) #T |J|,
```

并且保留覆盖数和 `δ^(2-σ-η/8192) #T` 的细重数上界。

`δ² #T` 不能凭直觉删掉。打印假设只给 `δ^η |J|` 时，要推出归一化质量，需要证明一个足够强的族基数上界。公共 CWA 不是方向分离假设，不能直接把族大小当作 `δ^-2` 来消去因子。当前 Proposition 6.5 的选区间、保质量、重数控制和框架准备是同时完成的，所以它能调用准备版；这不等于证明所有只满足打印两个假设的外部配置都能调用。根闭包中的实际 P6.5 仍走 prepared interval，新的任意配置 normalized interval 是重要但独立的兼容 API。

### 6. Lemma 6.7 为什么是 `σ-a`，以及与 `σ+a` 的强弱

当前 Roadmap 和 Lean 都证明上界 `|X_f(Y)| ≤ δ^(σ-a)`。当 `0 < δ < 1` 时，指数越大，幂越小；所以 `δ^(σ+a)` 小于 `δ^(σ-a)`，加号版本是更强的上界。减号版本来自水平 slice 覆盖数乘以纵向长度量级 `δ` 的计数，只能自然得到较大的 `δ^(σ-a)`。最终矛盾只需要这个较弱上界，因此当前 Roadmap 与 Lean 在符号上一致；不一致的是打印论文式 (6.11) 的加号版本。

### 7. 仿射归一化中 `k²` 与 `k` 的区别

令 `s=f(0)`、`k=1/(4(1+|s|))`，三维映射是

```text
A_s(x,y,z) = (k(x+sy), ky, z).
```

中心化斜率为 `f̃(z)=f(z)-s`。令二维线性映射 `B_k(u,z)=(ku,z)`，即只把第一坐标乘 k、保留第二坐标 z。直接代入有

```text
π_{f̃}(A_s(x,y,z))
  = (k(x+sy)+(f(z)-s)ky, z)
  = (k(x+f(z)y), z)
  = B_k(π_f(x,y,z)).
```

这里的 `B_k` 只作用于二维投影平面：第一坐标乘 k，z 坐标不变；不能把整个二维向量 `(u,z)` 都乘 k。三维雅可比来自 x、y 两个方向同时乘以 k，行列式为 `k²`，所以体积、密度和 CWA 常数搬运付出 `k²` 代价。扭曲投影是二维面积，只在水平投影坐标上乘 k，面积倍数是 `k`。只把斜率改成 `f-f(0)` 而不动族和 shading，得不到这个面积比较。

Lean 终端不是另选一份配置：它在实际 P6.5 输出中选宽度 `1/4` 的 slab，至少保留 `1/12` 的指标质量，做上述仿射、重新成管和去近管选择；refinement 记录保存源指标单射、精确轴线像、shading 包含关系以及 `analysisSlope = f.centered`。源尺度 cutoff 预先控制 `1+|f(0)|` 的小幂增长，使 `k²` 和 `k` 的成本能被损失预算吸收。

### 8. `f(0)=0` 与纵向位置为什么独立

`f(0)=0` 是斜率函数的截距归一化，处理的是扭曲投影 `x+f(z)y` 中由常数斜率偏移产生的坐标尺度。线段纵向位置处理的是单位线段中心沿自身支撑直线可以落在不同高度。即使两根管有完全相同的四维支撑线参数 `(a,b,c,d)`，其单位线段也可以沿该直线平移；参数 Frostman 会把它们计入近参数类，但一个固定单位粗管不一定同时包住两段。

两个反例分别针对两个失败方向。斜率偏移反例允许 `f(z)=s+z`，说明要求同一个统一 cutoff 对任意截距偏移和普通单位粗管条件成立会失败。纵向位置反例即使固定 `f(z)=z`、从而已有 `f(0)=0`，仍通过不同中心高度说明普通长度 1 粗管体积测试不足以推出统一下界。二者都没有 CWA 证书，也不在最终正向证明中；它们否定的是未修正的普通单位粗管、任意纵向位置或任意截距版本，并不否定长度 32 粗测试路线和最终 Theorem 5.2。

### 9. 长度 32 修改了什么，`128000` 来自哪里，基数前提在哪里消去

长度 32 修改的是粗测试集合：测试体使用普通单位细管中心放大的粗胶囊，轴长为 32，物理半径也按同一放大倍数改变；细管仍然是原来的单位线段，纵向位置不被强制共同中心化。

当参数球中一根细管与参考参数的 `∞` 距离不超过 r 时，有界竖直图几何把该细管在工作球内的部分纳入参考直线的 `20r` 横向邻域。为了给纵向位移留足余量，取物理半径 `R=20r`、轴长 32 的粗胶囊；源码中这对应先取半径 `R/32` 的单位胶囊再中心放大 32 倍。该胶囊体积至多 `320 R²`，所以

```text
320 * (20r)² = 320 * 400 * r² = 128000 r².
```

长度 32 Wolff 界给出参数类大小不超过 `128000 C r² #T`，固定常数再由小尺度 cutoff 吸收为参数 Frostman 损失。选中的 P7.1 主声明仍显式要求 `#T ≤ δ^{-q}`；后续 `pure_wz2_dilated_tube_wolff_lower_bound_in_vertical_chart` 在有界、本质不同条件下用固定球 packing 取得足够的 `δ^-7` 基数界，从而消去调用者给出的 q 前提。

### 10. JetCount 为什么只是已准备代表块的条件回传

JetCount 主声明不从一个裸参数集自动完成全部块选择、复制、均匀化和 cinematic 估计。它的输入已经包括局部完整块、每个已选三维参数对应的一根实际源代表管、复制集合及其分离/计数证书，以及四个已证明的分析输入：cinematic 估计、紧 subshading 选择、紧管 shading 投影面积估计、投影到所分配曲线邻域的包含关系。

每个折叠参数只选一根实际源管很关键。代表管的 `sourceIndex` 是单射，复制后的曲线族才能保持分离，固定分配重数常数 `B=12500000` 才有意义。若把同一折叠参数下的所有指标都复制过去，会得到重复函数和不受控的分配纤维，不能直接作为 cinematic 曲线族。该定理最后在代表管族上保留至少一半代表 shading 质量，并把复制数量、逐管质量和 cinematic 损失代入三次幂面积估计，再回传到原块。

### 11. Cinematic 量词顺序与 Lemma 7.12 的 `η → 4η`

Cinematic 输入先固定 cinematic 常数 `K≥1`、doubling 常数 `D≥1`、绝对 Katz-Tao 常数 `C_KT≥1`、图邻域倍数 `lambda≥1` 和绝对一致二阶 jet 上界 `M≥0`；然后给定 `ε>0`，选择 `δ₀ ≤ 1/lambda`；之后才是小尺度 δ 和具体函数族。绝对 C² 界、Katz-Tao 常数和邻域倍数不能在看到具体族以后改变。

Lemma 7.12 sharp 版先固定 `0<ε<1/100` 和 `1/100≤ρ_max≤1`，选择 `0<η_max≤ε`；对每个 `0<η≤η_max` 再选统一 `δ₀`。运行时还要求非空竖直图管族、参数界 `|a|,|b|≤12`、`|c|,|d|≤2`、有限常数 C 满足 `1≤C≤δ^-η`、参数 Frostman、总体 `δ^η`-dense shading、斜率窗口、`f.IsNonsingular` 和 `f(0)=0`。结论给 `ρ>δ^(1-ε²)` 和 subshading Z，使 Z 有 `δ^(4η)` 总体密度，并满足面积与 `ρ`-邻域覆盖的一尺度不等式。

保质量计算不是直接改写指数：正半窗口先以损失 `u=4η/3` 取得 `δ^(3u)=δ^(4η)` 密度；半窗口选择用 `u-η=η/3` 的余量支付固定损失，负半窗口再反射处理。

### 12. `ε=σ/4` 的最终矛盾与同一终端要求

闭合矛盾先对 `ε=σ/4` 调用独立 CWA 投影下界，得到 `0<η≤σ/4` 和尺度上界 `δ₀`。只有在这两个量固定后，才调用上界生产者，要求它以损失 η、尺度上限 δ₀ 返回终端。返回的 `data` 同时包含：

```text
data.family, data.shading, data.analysisSlope,
data.convex_wolff, data.dense, data.slope_window,
data.analysisSlope_nonsingular, data.analysisSlope_zero,
data.projection_upper.
```

下界就应用到这同一份族、shading 和斜率，于是

```text
δ^(σ/4) ≤ |X_f(Y)| ≤ δ^(σ-η).
```

由于 `η≤σ/4`，有 `σ-η≥3σ/4>σ/4`；当 `0<δ<1` 时指数越大幂越小，所以 `δ^(σ-η)<δ^(σ/4)`，矛盾。

下界 cutoff 必须先选。若先任意选一份上界配置，再临时为它挑选下界尺度，就不能保证那份配置满足统一下界定理的 δ 范围和损失约定。上下界还必须是同一个扭曲并集；换一份族、shading 或 f 后，即使符号相同也不能比较。最终 `PureWZ2Theorem5_2Unconditional` 没有外部 proof 输入：它从定理失败出发调用临界提取，再调用内部闭合的 `pure_wz2_no_critical_package`。

## 18 个节点的角色汇总

| 节点 | primary / 角色 | 我的理解 |
| --- | --- | --- |
| `W2MW` | `WZ2PaperPureCWAAtNearbyScales`，used definition | Definition 2.12 的公共命题，含本质不同、严格附近尺度和完整纤维。 |
| `W2L2_13` | 无 primary，unmatched | 一般继承引理没有独立 Lean 证明，不能用特定结构证书替代。 |
| `W2Sigma` | `PureWZ2Admissible`，used predicate | 主声明是 admissibility 谓词；临界 package 在提取证明中局部产生。 |
| `W2D6_1` | `WZ2PaperPureIsExtremal`，used definition | 极端配置字段集合，sigma 是显式参数；定义本身不证明存在性。 |
| `W2P6_2` | `pure_wz2_node03_rich_prop62_kernel`，used proof | 保存运行函数、实际粗细终端、重数、归一化和 re-entry 数据的强内核。 |
| `W2P6_3` | `pure_wz2_node04_reentrant_grains`，used proof | 在同一来源上给全局/局部 grains，并保留普通和裁剪 re-entry 数据。 |
| `W2P6_4` | `pure_wz2_left_line_c2_grains`，used proof | 闭合 C² grains 生产者，输出同配置模型条件、CWA、cubical shading 和 grains。 |
| `T5_2` | `WZ1ProjectionDichotomyConclusion`，unused interface | 完整一般二择一只是命题接口，不在根闭包；实际使用更具体 union 结果。 |
| `W2L6_6` | `pure_wz2_lemma66_prepared_interval`，used proof | 实际 P6.5 使用准备版；任意配置 normalized 版已证明但保留归一化质量和重数前提。 |
| `W2P6_5` | `pure_wz2_left_line_large_slope_retained`，used proof | 返回保留共同来源、终端几何、源/目标尺度和清理证书的大斜率构造。 |
| `W2L6_7` | `pure_wz2_left_line_normalized_projection`，used proof | 对实际 P6.5 终端做仿射、slab、重新成管和清理，给 CWA 与 `σ-a` 小投影。 |
| `W2Zero` | `pure_wz2_no_critical_package`，used proof | 证明任何正临界 package 都导致矛盾，不声明全局常数等于零。 |
| `W2JetCount` | `parameter_block_representative_cinematic_pullback`，used proof | 已准备代表块上的条件 cinematic 回传，不是完整裸参数提取定理。 |
| `W2L7_12` | `pure_wz2_lemma7_12_parameter_frostman_sharp_density`，used proof | 参数 Frostman 下的一尺度面积比较，输入 `δ^η`、输出 `δ^(4η)` subshading。 |
| `T7_2` | `Kakeya.Cinematic.wz2_uniformC2_input`，used proof | 固定常数和绝对二阶 jet 界后的统一 cinematic `L^(3/2)` 输入。 |
| `W2P7_1` | `pure_wz2_proposition7_1_dilated_tube_wolff`，used proof | 长度 32 粗胶囊、归一化斜率和显式基数预算下的扭曲投影下界。 |
| `W2P6_8` | `pure_wz2_convex_wolff_lower_bound_via_dilated_tubes`，used proof | CWA 经长度 32 凸粗测试和修正 P7.1 得到同终端投影下界。 |
| `W2T5_2` | `PureWZ2Theorem5_2Unconditional`，used proof | 公共最终离散并集体积估计；非空显式写出，无外部中间证明参数。 |

## 17 条 Roadmap 连线核对

| Roadmap 线 | 分类 | 源码路径含义 |
| --- | --- | --- |
| `W2MW → W2L2_13` | `unmapped` | Lemma 2.13 无 primary，不能比较路径。 |
| `W2Sigma → W2D6_1` | `different-route` | 极端定义接受显式 sigma，不引用 admissibility 谓词。 |
| `W2L2_13 → W2P6_2` | `unmapped` | 一般继承节点无 primary，实际只有特定 re-entry 证书。 |
| `W2D6_1 → W2P6_2` | `actual` | 6 步类型/结构路径，rich kernel 经 critical package 和极端配置结构引用定义。 |
| `W2P6_2 → W2P6_3` | `actual` | 1 步证明值引用，reentrant grains 吃 rich Proposition 6.2 kernel。 |
| `W2P6_3 → W2P6_4` | `actual` | 1 步证明值引用，C² 闭合入口调用 reentrant grains。 |
| `T5_2 → W2P6_4` | `outside-root` | 完整二择一主声明不在根闭包；实际走具体 union theorem。 |
| `W2P6_4 → W2L6_6` | `different-route` | Lemma 6.6 的类型提配置，但证明不调用 C² 生产者。 |
| `W2L6_6 → W2P6_5` | `actual` | 7 步路径，经大斜率组装和 `pure_wz2_lemma66_prepared` 到 prepared interval。 |
| `W2P6_5 → W2L6_7` | `actual` | 1 步直接引用，归一化终端消费 retained 大斜率终端。 |
| `W2L6_7 → W2Zero` | `actual` | 1 步直接引用，矛盾闭合把归一化上界生产者填入通用矛盾。 |
| `W2JetCount → W2L7_12` | `actual` | 1 步证明值引用，sharp density 入口使用代表块回传。 |
| `T7_2 → W2L7_12` | `actual` | 2 步路径，经 `pyz_input` 到统一 cinematic 输入。 |
| `W2L7_12 → W2P7_1` | `actual` | 3 步路径，修正粗管下界经参数 Frostman 版和旧一尺度入口到 sharp 版。 |
| `W2P7_1 → W2P6_8` | `actual` | 2 步路径，CWA 下界调用竖直图 packing 入口，再调用长度 32 P7.1。 |
| `W2P6_8 → W2Zero` | `actual` | 2 步路径，矛盾接口使用独立 CWA 下界。 |
| `W2Zero → W2T5_2` | `actual` | 1 步直接引用，最终定理从失败提取正 package 后调用矛盾。 |

计数与证据一致：17 条 Roadmap 线中 12 条 `actual`、2 条 `unmapped`、2 条 `different-route`、1 条 `outside-root`。Lean 层也有 17 条线，全部被比较器标为 `agree`；共同直接端点对是 12 对。Lean 在 Core 直接图中新增的 5 对是 `W2MW→W2Sigma`、`W2MW→W2D6_1`、`W2Sigma→W2P6_4`、`W2P6_4→W2P6_5`、`W2MW→W2L6_6`，它们在完整 Roadmap 中可达，不应称为 `Lean only`。

## 需要修订的具体句子与建议

1. 第 415-418 行关于任意配置 Lemma 6.6 的位置最容易被误读。当前句子“当前还独立构造了一份……对每个 J，它调用归一化的 Lemma 6.6”紧接在 P6.4 主路径之后，读者可能以为根闭包的 P6.5 已改用 normalized interval。证据显示 prepared interval 仍是实际 P6.5 依赖，而 `pure_wz2_lemma66_normalized_interval` 和 prescribed-intervals 闭合入口当前不是根路径主声明。建议改成：

```text
仓库还提供一个独立的任意给定配置 API：全局细管重数来源可先固定，之后对每个满足归一化质量、覆盖和细重数条件的 J 调用 normalized Lemma 6.6，且不重新选择 C² 配置。该 API 去掉了框架前提，但当前 Core 根闭包中的 Proposition 6.5 仍通过 prepared interval 路线调用准备版；二者应分别叙述。
```

2. 第 163-165 行“两种证书的转换由相应的选择与去近管证明完成”略泛。源码中的一个明确方向是在足够小尺度下由论文 centered-dilation 定义推出交叠体积定义；并没有在这句话里说明 cutoff 和方向性。建议改成：

```text
在 δ≤1/100000 时，普通论文本质不同可由 `WZ2PaperOrdinaryIsEssentiallyDistinct.overlapDistinct` 推出交叠体积意义下的本质不同；另一些清理步骤只保证所选子族具有所需证书。这里不应把两个定义理解为无条件等价。
```

3. 第 442-446 行“垂直线”可能与三维竖直图中的 vertical chart 混淆。建议一般叙述全部改为“过原点且方向为 `v⊥` 的直线”和“方向为 v 的仿射线”；只在 F/G 示例中说该例表现为竖直线和水平仿射线。

4. 第 435-440 行把 Lean 的 `center,radius` 条件翻译成“正长度区间 J”是合理数学翻译，但若强调 literal，可补一句：

```text
Lean 源码用球心 `center` 和半径 `radius` 编码这段截线，条件 `δ^-η ρ ≤ 2*radius` 对应这里的长度下界。
```

5. 第 613 行“擦去构造数据”、第 1024 行“追着它选择”、第 1192 行“倒回”口语色彩较强。建议分别改为“只取该结构中的论文结论”、“在配置已经选定后再试图选择”、“改写为”。“支付损失”可保留；若全文想更正式，可统一改成“纳入误差预算”。

6. 主稿已经正确区分定义节点、命题接口和范围内证明，建议在结论检索表附近再显性强调一次：`used-proof` 只表示该声明在根闭包中有编译证明依赖，不自动表示图卡自然语言的完整一般版本已证明。这个观念贯穿全文，但在读者只看表格时仍可能被简化成“已证明/未证明”的二元标签。

## 最终判断

我能按自己的论证语言复述整条 Core proof DAG：反证提取正临界指数，左侧构造 C² grains、准备 slab、获得大斜率并归一化出小投影终端；右侧独立证明 CWA 经长度 32 粗测试到参数 Frostman、一尺度 cinematic 估计和投影下界；最后在同一个 `T,Y,f` 上以 `σ/4` 对 `σ-η` 产生矛盾。当前主稿的核心数学陈述、依赖分类和源码范围说明可以支撑这条叙述。最值得修的是把“根证明实际使用的 prepared Lemma 6.6”和“已证明但不在该根路径上的任意配置 normalized API”再隔开一句，以及把本质不同转换的方向性和 cutoff 写得更 literal。

## 主稿修订后的复核确认

已重新核对修订后的关键段落：第 163-168 行现在明确只在 `0<δ≤1/100000` 时陈述普通论文本质不同到交叠体积条件的方向性推导；第 418-428 行明确区分了被实际 Proposition 6.5 使用的全局 fine-cap producer，与当前根证明未调用的 prescribed-intervals 入口和任意配置 normalized interval 定理；第 452-454 行用 `center/radius` 和 `2R` 对应 Roadmap 的区间长度；第 455-461 行把方位改成一般的 `v⊥` 过原点直线与方向为 `v` 的仿射线；第 703-705 行新增 `B_k(u,z)=(ku,z)` 和 `π_{f̃}∘A_s=B_k∘π_f`；第 1284-1285 行也明确 `used-proof` 不认证图卡的完整一般版本。

我确认这里的二维投影关系应理解为：`B_k` 只把投影平面的第一坐标 `u=x+f(z)y` 乘成 `ku`，第二坐标仍是 `z`，所以面积倍数为 `k`；它不是对标量乘法 `k(u,z)=(ku,kz)` 的简写。三维空间映射 `A_s` 同时缩放 x、y 两个坐标，体积 Jacobian 才是 `k²`。修订后的主稿已经把这两个倍数、fine-cap producer/兼容 endpoint 的根使用状态、本质不同定义的方向和 cutoff、以及 WZ1 方位差异分开说清楚。
