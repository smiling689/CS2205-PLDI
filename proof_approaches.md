# PL 证明方法与技巧总览

本文汇总 `pl` 目录下所有 Coq 文件中出现、且在证明过程中反复使用的技巧与战术。每条技巧都结合了原文件中的示例或注释，说明“什么时候用、为什么用”，方便在复现或扩展证明时快速定位思路。

## 1. 证明脚手架与基本指令
- `intros` 将全称量词和蕴含前提逐一引入环境，是大多数证明脚本的起点；配合 `pose proof` 可立即实例化外部定理（例如把 `sqr_pos` 应用于具体表达式 `x - y`）（`pl/SimpleProofsAndDefs.v:132`, `pl/SimpleProofsAndDefs.v:133`）。
- `unfold` 可将自定义函数或谓词的定义直接展开，化为算术或逻辑目标，再交给自动化战术（如展开 `nonneg`、`plus_one` 之后用 `lia` 收尾）（`pl/SimpleProofsAndDefs.v:249`）。
- `simpl` 与 `reflexivity` 组合，可在递归定义或 `Fixpoint` 的模式匹配展开后立即判定等式成立（如计算树高或列表拼接的示例）（`pl/SimpleInductiveType.v:53`，`pl/MoreInductiveType.v:632`）。
- `assumption`、`apply` 在前提已经满足目标类型时直接结束子目标，常与 `split` 生成的子目标配套（`pl/SimpleProofsAndDefs.v:475`）。

## 2. 算术自动化与辅助算子
- `lia` 负责线性整数（不等式、等式）自动化，能一行解决“鸡兔同笼”“年龄问题”等线性约束（`pl/SimpleProofsAndDefs.v:45`, `pl/SimpleProofsAndDefs.v:99`）。
- `nia` 扩展到非线性整数推理，可先用 `Fail nia` 判断目标是否超出能力，再辅以人为 `pose proof` 或代数变换后重新求解（`pl/SimpleProofsAndDefs.v:108`, `pl/SimpleProofsAndDefs.v:133`）。
- `replace ... with ... by ...` 可以显式给出代数恒等式，让 `nia`/`lia` 有合适的推理入口（如证明立方函数单调时把差值改写为乘积形式）（`pl/HighOrder.v:162`）。
- `pose proof` & `specialize`：前者把通用定理放入上下文，后者把“对任意 `x`”的前提特化成“对当前 `x0`”；两个指令频繁配合 `nia`/`lia` 或逻辑推理使用（`pl/SimpleProofsAndDefs.v:133`, `pl/SimpleProofsAndDefs.v:337`, `pl/Logic.v:667`）。
- `assert` 与 `revert` 用于加强归纳假设或回退尚未泛化的变量：`assert` 先补一个需要的子结论（如跨两步归纳前先证明“加强命题”），`revert` 则把当前目标里的变量重新移回量词位置再做归纳（`pl/BuiltInNat.v:382`, `pl/MoreInductiveType.v:748`）。

## 3. 命题逻辑结构化
- `split`/`destruct` 分别负责构造与拆分合取；`destruct H as [H1 H2]` 在解包 `P /\ Q` 时还能顺便命名新前提（`pl/Logic.v:16`, `pl/Logic.v:34`）。
- `left`/`right`、`exists` 则分别构造析取与存在量词，结合 `destruct` 完成分类讨论（`pl/Logic.v:131`, `pl/Logic.v:583`）。
- `tauto` 可在命题逻辑层面自动完成冗长的排列组合推理，尤其适合“真假都能推出矛盾”“逆否命题”等场景（`pl/SimpleProofsAndDefs.v:405`, `pl/Logic.v:705`）。
- `classic` 提供排中律，把不可判定命题拆成“成立/不成立”两类后分别求解（`pl/Logic.v:775`）。
- `pose proof`、`specialize` 还能与 `forall x, ...` 配合，将“任意元素”性质转化为当前目标需要的具体实例（`pl/Logic.v:667`）。

## 4. 结构化归纳与列表/自然数证明
- `induction n; simpl` 是自然数归纳的标准模板：奠基步直接 `reflexivity`，归纳步利用先前的辅助引理（例如先证明 `add_0_r`、`add_succ_r` 再完成加法交换律）（`pl/BuiltInNat.v:43`, `pl/BuiltInNat.v:66`）。
- 当递归函数跨两级下降（如 `Nat.div2`）时，需要“强化版”归纳：`assert` 加强命题、`split` 构造 `(Pn /\ Pn+1)` 的目标，再在归纳步用 `tauto`/`destruct` 逐块传递（`pl/BuiltInNat.v:382`, `pl/BuiltInNat.v:387`）。
- 列表证明通常“对左参数做归纳”，因为 `app` 的递归只在左边展开；若尝试对右参数归纳，会缺少可用的归纳假设，这在 `app_assoc` 的讨论中被特别强调（`pl/MoreInductiveType.v:601`）。
- `revert` 或将“待比较的第二棵树/第二个列表”保留在目标中（`intros` 只引入首个参数），可避免归纳假设过于具体无法套用，这在 `tree_reverse_inj`、`same_structure_same_height` 的加强归纳里都有示范（`pl/MoreInductiveType.v:178`, `pl/MoreInductiveType.v:428`）。

## 5. 递归数据的分类讨论与构造子性质
- `destruct t` 对归纳类型做穷举，并可配合 `+/-/*` 子弹把两个以上分支的脚本隔离（`pl/SimpleInductiveType.v:153`）。
- `discriminate` 基于构造子不相交性直接推出矛盾（如 `Leaf = Node ...` 不成立），不需要手写等式化简（`pl/SimpleInductiveType.v:142`）。
- `injection` 借助构造子单射，把等式 `Node l1 v1 r1 = Node l2 v2 r2` 拆成多个子等式，有选择地命名/忽略（`pl/SimpleInductiveType.v:98`, `pl/SimpleInductiveType.v:130`）。
- `Fail discriminate`、`Abort` 可以记录“某路径不可行”的信息，以免后续误用该 tactic（`pl/SimpleInductiveType.v:181`, `pl/SimpleProofsAndDefs.v:115`）。
- `repeat rewrite` 或 `rewrite ... in ...` 则负责把 `injection`/`discriminate` 生成的新等式真正用到目标上（`pl/SimpleInductiveType.v:205`）。

## 6. 高阶函数与性质复用
- 定义高阶函数（如 `Zcomp`、`shift_left1`、`shift_up1`）后，可通过 `mono_compose`、`preserved_by_shifting_up` 之类的引理把“单调”“始终非负”等性质传递给组合函数（`pl/HighOrder.v:125`, `pl/HighOrder.v:224`）。
- `assert (mono (fun x => x - 1)) as H_minus` 这类写法把后续证明需要的子组件折叠为命名前提，和 `pose proof cube_mono` 一起充当“模块化积木”（`pl/HighOrder.v:282`, `pl/HighOrder.v:298`）。
- `replace`、`lia`/`nia` 结合，可证明诸如“立方函数单调”这类需要显式代数恒等式的事实（`pl/HighOrder.v:162`）。

## 7. 重写、等价关系与 `Proper`
- `rewrite H`, `rewrite <- H` 不只适用于普通等式，也能依靠“结构化等价”的 `Instance`（如 `Equivalence same_sgn`）在自定义关系下自动发挥作用（`pl/AlgebraicStructure.v:128`, `pl/AlgebraicStructure.v:144`）。
- `symmetry`、`transitivity` 战术可以在 `pointwise_relation` 这样的高阶关系里直接使用，因为文件中已注册了对应的 `Reflexive`/`Symmetric`/`Transitive` 实例（`pl/AlgebraicStructure.v:210`, `pl/AlgebraicStructure.v:226`）。
- 为允许在表达式语义里面做“带语义的重写”，需要提供 `Proper (R ==> R ==> R) f` 实例，如 `Proper_congr_Mod5_Zsub`、`lt_sem_congr`、`add_sem_congr` 等；一旦注册，`rewrite H` 就可以跨过 `Z.sub`、`lt_sem`、`eval_expr_int` 等函数（`pl/AlgebraicStructure.v:437`, `pl/DenotationsAsRels.v:100`, `pl/DenotationsOfExpr.v:390`）。
- `setoid_rewrite` 是在自定义等价（例如集合等价）下的“批量 rewrite”，特别适合把 `S1`、`S2` 的语义定义重写成实际的算术约束（`pl/SetsAndRels.v:84`）。

## 8. 集合与关系推理
- `Sets_unfold`/`sets_unfold` 把 `∪/∩/∘` 等符号重新展开为存在量词与谓词逻辑，从而转化为熟悉的命题证明（`pl/SetsAndRels.v:77`）。
- `apply Sets_included_indexed_intersect`、`apply Sets_indexed_union_included` 等库定理负责处理“无限交/并”与索引族；通常先 `rewrite` 标准等式，再逐元素证明包含关系（`pl/DenotationsAsRels.v:458`, `pl/SetsAndRels.v:568`）。
- `exists (x + 1)` 之类的构造证明出现在集合语义中，用来把“关系连接”化为实际的中间状态/变量（`pl/SetsAndRels.v:93`）。
- 关系代数性质（结合律/左右单位/分配律）可直接复用 `SetsClass` 的引理或自己用 `Sets_unfold` 展开手证，例如 `Rels22_concat_assoc`、`Rels22_concat_union_distr_r`（`pl/SetsAndRels.v:647`, `pl/SetsAndRels.v:679`）。

## 9. 指称语义专用方法
- 对表达式语义的保结构证明，可以“先在语义层给出 `..._sem_congr`，再在语法层声明 `EAdd/EWhile` 等构造子的 `Instance`”，这样 `apply sub_sem_congr`/`apply lt_sem_congr` 就能直接把子表达式的等价性提升到父节点（`pl/DenotationsOfExpr.v:404`, `pl/DenotationsOfExpr.v:470`, `pl/DenotationsAsRels.v:100`）。
- 控制流语句的等价通常利用关系运算的代数性质，例如顺序语句语义通过 `apply Rels_concat_assoc` 化简，循环语义通过 `while_sem_congr`、`while_unroll1` 把展开与索引并联动起来（`pl/DenotationsAsRels.v:443`, `pl/DenotationsAsRels.v:525`, `pl/DenotationsAsRels.v:536`）。
- 当需要描述“组合语句整体等价”时，可直接 `apply Sets_equiv_Sets_included; split`，把等号目标拆成两个包含，分别调用 `Sets_indexed_union_included`、`Sets_union_included` 等工具（`pl/DenotationsAsRels.v:458`, `pl/DenotationsAsRels.v:544`）。

## 10. 逻辑-算术混合技巧
- `lia`/`nia` 与逻辑战术的组合十分常见：先用 `pose proof` 拿到数值断言，再交给 `tauto` 整理布尔结构（如 `logic_ex1` 先把“非负/偶数”分量化，再 `tauto` 消去逻辑部分）（`pl/SimpleProofsAndDefs.v:389`, `pl/SimpleProofsAndDefs.v:402`）。
- `apply` 现成引理（如 `same_sgn_trans`、`same_sgn_symm`）可构建“多步传递”链路，也可以内联 `apply ... with ...` 在一行里完成多级推导（`pl/AlgebraicStructure.v:85`）。
- `intuition congruence` 是 `intuition` 的派生形式，同时做布尔推理与等式合一，适合列表 `In` 一类需要同时处理析取和等式的目标（`pl/MoreInductiveType.v:1026`）。

## 11. 调试、排版与结构化
- `Fail` 用于刻意触发失败，说明当前战术不适用（例如 `Fail discriminate` 强调“不是每个等式都能靠构造子矛盾解决”），`Abort` 则暂时放弃无望脚本（`pl/SimpleInductiveType.v:181`, `pl/SimpleProofsAndDefs.v:115`）。
- Coq 的 `+ - *` 子弹和注释并排方式示范了如何让多分支归纳更易读，可在复杂 `destruct`/`induction` 中保持清晰分隔（`pl/SimpleInductiveType.v:155`）。

通过以上方法，你可以针对 `pl` 目录的所有示例复现实验室里的证明思路：先用 `intros`/`unfold` 明确上下文，再依据目标类型选择“逻辑拆分”“算术自动化”“结构归纳”“集合或语义层的 congruence”中的合适套路；必要时记得用 `pose proof`、`assert`、`revert` 或 `Proper` 实例把欠缺的桥梁补齐，最后用 `lia`/`tauto` 等自动化战术封口。文件中给出的每一条指令、每一个实例，都是为了让这些套路可直接复用。***
