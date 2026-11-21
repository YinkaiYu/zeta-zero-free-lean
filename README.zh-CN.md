# 黎曼 ζ 函数经典无零点区的紧凑 Lean 4 证明

**Yin-Kai Yu (余荫铠)** · GPT-6.2 Astra · ChatGPT Desktop  
[英文论文 PDF](paper/zero-free-region.pdf) · [论文 LaTeX 源码](paper/zero-free-region.tex) · [最终 Lean 证明](Solution.lean) · [赛事提交 #96295](https://riemann.verifytask.cn/api/attempt/96295)

## 这项成果解决什么问题

黎曼 ζ 函数把复分析与素数分布联系起来。经典无零点区定理说，在复平面上，靠近直线 $`\mathrm{Re}(s)=1`$ 的一条区域里，ζ 函数没有零点。这条区域的宽度随虚部的绝对值增大而缓慢收窄。这样的估计是研究素数计数误差的工具。黎曼猜想关心更强的命题：所有非平凡零点都在 $`\mathrm{Re}(s)=\tfrac12`$ 上。本仓库给出的是上述经典区域的无条件证明。

Agentic Science Challenge 把 Levent Alpöge 的形式化项目中的五个定理列为独立赛题，Core 1 指第一题，即 ζ 函数的经典无零点区。每位参赛者面对同一个 Lean 4 定理陈述，可以调用固定版本的数学库 Mathlib。Lean 内核检查证明能否推出该陈述，赛事再用规范化词元衡量证明源码的长度。这里的一项纪录就是在同一题上，用更少的词元完成可验证的证明。网页上的绿色曲线合计五道题各自的最佳结果。

## 我们证明的界

这份证明给出了一个显式常数。对任意复数 $`s=\sigma+it\ne1`$，

```math
\sigma \ge 1-\frac{2^{-20}}{\log(|t|+2)} \quad\Longrightarrow\quad \zeta(s)\ne 0.
```

赛事参考证明的依赖闭包有 21 个 Lean 文件、21,641 个规范化词元。2026 年 11 月 22 日北京时间 06:32:56 的公开榜单快照中，**#96295 以单文件 2,388 词元位居 Core 1 第一，相对基线压缩 88.97%，正式得分 65.873483**。仓库收录起始对照版和四个刷新纪录的提交，每份源码均从对应的实际上传包中提取。[官方题面](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729) · [赛事曲线](https://riemann.verifytask.cn/) · [带时间和来源的成绩记录](records/results.json)

## 原版证明的瓶颈：下游只用一个零点，上游却给出了全部零点

赛事以 Levent Alpöge 的 `Formalism.ZF.zeroFreeRegion` 为基线。要理解它的长度，可以从最终装配式往回读。原版用 `localZeroExpansionOfFactorization zeroFactorization logDerivBoundOnBall` 得到局部 Landau 估计。为提供第一个输入，`ZeroFactor.lean` 的 `exists_factorization_of_sum_order` 要处理零点集合、各点的消失阶数以及剥离后的全纯余因子。随后，`LandauLocalOf.lean` 的 `hasDerivAt_prod_sub_pow` 要对形如 ∏(w − ρ)ᵐ 的有限乘积求导，把它变成一串倒数项。第二个输入又需要对无零点余因子作对数导数估计。这些步骤保留了每个零点的位置和重数。最终的三高度反证只用到一个指定零点的倒数贡献，以及其余贡献的符号。这一信息差给出了压缩证明的切入点。[原作者源码说明](https://alpo.ge/remark.pdf) · [官方基线与定理陈述](https://play.bohrium.com/challenges/lean-4-verification-rh-core-pillar-1-5-classical-z-c7f72729)

## 核心推导：保留一个零点，把其余工作交给增长界

**1. 先写出三高度论证真正需要的局部引理。** 设 f 是整函数，$`f(0)\ne0`$，所有零点的实部均非正。在半径 1/2 的闭圆盘上假设 $`|f(w)|\le B|f(0)|`$，故 B ≥ 1。取 x = 0，或指定一个满足 $`|\rho|\le\tfrac16`$ 的零点，并取 $`x\le-\mathrm{Re}(1/\rho)`$。提交中的 `ClassicalZFR.landau` 一次证明两种情形。

```math
x-\mathrm{Re}\!\left(\frac{f'(0)}{f(0)}\right)\le 24(\log B+1).
```

**2. 剥离一个零点，增长界为什么会减半？** 令 g 为 f 在 ρ 处的解析差商。Mathlib 的 `differentiableOn_dslope` 保证 g 在被除去的点仍然可微，`sub_smul_dslope_of_zero` 给出 f(w) = (w − ρ)g(w)。在外圆 ∣u∣ = 1/2 上，$`|u-\rho|\ge\tfrac12-\tfrac16=\tfrac13\ge2|\rho|`$。再用 $`|f(0)|=|\rho|\,|g(0)|`$，得到

```math
|g(u)|=\frac{|f(u)|}{|u-\rho|}\le\frac{B|\rho|\,|g(0)|}{2|\rho|}=\frac B2\,|g(0)|.
```

最大模原理把这个界从圆周推广到闭圆盘。与此同时，乘积的对数导数给出 $`\frac{f'(0)}{f(0)}=-\frac1\rho+\frac{g'(0)}{g(0)}`$。见证条件 $`x\le-\mathrm{Re}(1/\rho)`$ 恰好抵消被剥离的项，余下只须对 g 取 x = 0 证明同一个引理。若 ρ 是重零点，它可以在下一轮再次出现。这样就省去了预先枚举重数和对整个有限乘积求导的 Lean 声明。

早期归档版以 $`B<2^n`$ 控制递归。最终版取自然数 $`n>2B`$；在后继步 n = m + 1 时，由 B ≥ 1 和 2B < m + 1 得 B < m，恰好就是下一步所需的 2(B/2) < m。递归返回后，用 log(B/2) ≤ log B 放宽上界即可。源码注明这一步单调性改写参考了 Pi 的公开提交。[最终圆盘引理](Solution.lean#L75-L119) · [改写归纳参数的完整 Diff](diffs/96285-to-96293.diff)

**3. 无零点分支中的 24 从哪里来？** 没有可用见证时，x = 0；内圆盘中任一零点都有 −Re(1/ρ) ≥ 0，本可充当见证。因此 f′/f 在这个圆盘全纯。取原函数 G，令 G(0) = 0。由 f = f(0) exp(G) 得 Re G ≤ log B。记 A = log B + 1。在半径 1/6 的圆盘上应用 `borelCaratheodory_zero`，代入 ∣w∣ = 1/12 即得 ∣G(w)∣ ≤ 2A。再由 Cauchy 导数估计得到 $`|G'(0)|\le\frac{2A}{1/12}=24A`$，而 G′(0) = f′(0)/f(0)。在 Lean 中，最后这一步直接调用 `norm_deriv_le_of_forall_mem_sphere_norm_le`。[从邻域估计改为圆周估计的 Diff](diffs/96281-to-96285.diff)

**4. 为什么同一个引理足以覆盖三个高度？** 取 F 为 (s − 1)ζ(s) 的整函数延拓。Abel 求和用同一个 Mellin 余项给出半平面上的二次增长界，也推出假想零点 β + it 满足 ∣t∣ ≥ 1/2。令 $`L=\log(|t|+2)`$，$`d=2^{-20}/L`$，a = β + 5d。在 a、a + it、a + 2it 三处平移 F。中间圆盘里的指定零点正好是 −5d，按权重 4 贡献 4/(5d)。实中心的极点按权重 3 至多贡献 3/(4d)，相减留下 1/(20d)。

其余两组量各有独立的控制方法。模一特征的 L 函数乘积给出三个中心处 log∣F∣ 的加权下界。von Mangoldt 系数非负，恒等式 $`3+4\cos\theta+\cos(2\theta)=2(1+\cos\theta)^2`$ 则保证对数导数的加权级数非负。代入上述 d 后，剩余不等式要求 $`(2^{20}-11520)L<103860`$，但 $`L\ge\log 2>\tfrac12`$ 使左边大于 518528，矛盾。[逐项常数核算](paper/three-heights.tex)

## 88.97% 是怎样算出来的

正式基线包含依赖闭包中的 21 个 Lean 文件、21,641 个规范化词元。到了归档起点 #96267，整函数和单零点路线已在一个文件中实现，计 3,128 个词元，比基线少 18,513 个。下表的四份实测补丁又依次省下 236、168、300、36 个，共 740 个。两段加起来正好是 19,253 个，除以 21,641 得 **88.97%**。前段是两份完整实现的比较；后段可以逐份应用补丁复算。一次补丁包含多种改写，表中节省量按整份补丁计。[提交源码与测量记录](records/results.json)

## 每次突破对应哪一段改动

| 完整 Lean 差异 | 结果词元 | 比本组上一份少 | 比当时榜首少 | 主要改动 |
|---|---:|---:|---:|---|
| [#96267 → #96281](diffs/96267-to-96281.diff) | 2,892 | 236 | 132 | 直接以 von Mangoldt 级数的实部组织三个可和性证明 |
| [#96281 → #96285](diffs/96281-to-96285.diff) | 2,724 | 168 | 38 | 在固定圆周上用 Cauchy 导数估计，统一三处对数导数的复数恒等式 |
| [#96285 → #96293](diffs/96285-to-96293.diff) | 2,424 | 300 | 262 | 用 $`n>2B`$ 重写差商归纳，把依赖外部参数的增长估计改成内在二次界 |
| [#96293 → #96295](diffs/96293-to-96295.diff) | 2,388 | 36 | 36 | 匹配 Abel 求和的因式形式，在归纳假设内改写增长界，用平方非负直接收尾 |

每一行的节省量对应整份差异。前三次突破均推动五项合计曲线的两位小数读数，最后一次把 Core 1 纪录再降了 36 个词元，合计曲线前后均显示 41.61%。[原始版本](snapshots/) · [成绩及 SHA-256](records/results.json)

## 本地复核

五个 Git 标签分别保存五次提交的证明。Git 提交时间是本次建档时间，实际参赛提交时间见成绩记录。[在 GitHub 逐行对照首末两版](https://github.com/YinkaiYu/zeta-zero-free-lean/compare/attempt-96267...attempt-96295)

安装 Git、Python 3 和 [Lean 工具链管理器 elan](https://github.com/leanprover/elan)，从仓库根目录执行：

```sh
python tools/check_archive.py
lake exe cache get Mathlib.Analysis.Complex.HalfPlane Mathlib.Analysis.MellinTransform Mathlib.NumberTheory.LSeries.SumCoeff Mathlib.NumberTheory.LSeries.Nonvanishing Mathlib.NumberTheory.Harmonic.ZetaAsymp Mathlib.Analysis.Complex.BorelCaratheodory Mathlib.Analysis.Complex.HasPrimitives Mathlib.Analysis.Calculus.LogDeriv
lake build
lake env lean Audit.lean
lake env leanchecker Solution
```

第一条命令会重算五份源码的词元数和 SHA-256，并顺序应用四份补丁，验证每一步都能逐字节还原下一次提交。工程固定使用 Lean 4.34.1 和题目指定的 Mathlib 修订。类型检查文件核对完整定理陈述并列出依赖公理，结果为 `propext`、`Classical.choice`、`Quot.sound`。最后一条命令重放已编译的证明。[类型检查](Audit.lean) · [依赖版本](lake-manifest.json)

这条路线继承 de la Vallée Poussin 的经典三高度论证。赛事参考形式化来自 Levent Alpöge。差商剥离后用单调性放宽增长界的一步，在实际提交的源码中已注明参考 Pi 的公开提交 #96263。论文给出了每项工程改写对应的数学式、Mathlib 声明和完整差异。[Alpöge 的源码说明](https://alpo.ge/remark.pdf) · [Pi 的公开提交](https://riemann.verifytask.cn/api/attempt/96263) · [固定版本的 Mathlib](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612)
