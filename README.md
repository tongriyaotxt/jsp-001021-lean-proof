# Justin Sun Prize — JSP-001021 Lean 4 形式化证明

## 题目

**JSP-001021**: How large a transitive subtournament must every tournament of prescribed order contain?
（每个 n 阶竞赛图必含多大的传递子竞赛图？）

来源：<https://github.com/TheJustinSunPrize/awards> · `problems/catalog-1001-1022.md#JSP-001021`
（注：若上游完成 Fermat 插入重编号，本题在新编号下为 JSP-001022。）

## 结论（Erdős–Moser 下界的机器可验证形式化）

**每个 n 阶竞赛图都含有至少 ⌊log₂ n⌋ + 1 个顶点的传递子竞赛图。**

形式化陈述（`Jsp001021.lean`，纯 **Lean 4 core**，零依赖，不需要 Mathlib）：

```lean
theorem jsp_001021 (n : Nat) (hn : 1 ≤ n) (E : Fin n → Fin n → Bool)
    (hirr : ∀ i, E i i = false)
    (htot : ∀ i j, i ≠ j → E i j = !E j i) :
    ∃ s : List (Fin n), s.Nodup ∧ Nat.log2 n + 1 ≤ s.length ∧
      ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, E a b = true → E b c = true → E a c = true
```

- 竞赛图：`E : Fin n → Fin n → Bool`，自反为假、不同顶点间恰有一个方向（`htot` 给出全序非对称性）。
- 传递子竞赛图：无重复顶点列表 `s`，其上的导出关系传递（配合竞赛图公理即为全序）。
- `Nat.log2 n` 即 ⌊log₂ n⌋（n ≥ 1）。

## 证明思路（经典 Erdős–Moser 归纳）

对 n 强归纳。n = 1 平凡。n ≥ 2 时：出度总和为 n(n−1)/2（每个无序对恰贡献一条边），
故存在顶点 v 出度 m ≥ (n−1)/2。对其出邻域（m 阶导出竞赛图，1 ≤ m < n）用归纳假设，
得到长度 ≥ ⌊log₂ m⌋ + 1 的传递列表；由于 v 击败其中所有顶点，前面接上 v 仍传递，
长度 ≥ ⌊log₂ m⌋ + 2 ≥ ⌊log₂ n⌋ + 1（由 2m ≥ n−1 推得 m ≥ 2^(⌊log₂ n⌋−1)）。

## 构建与验证

安装 Lean 4（本证明在 v4.34.0 上验证通过；见 `lean-toolchain`）后：

```bash
lean Jsp001021.lean
```

公理审计（文件末尾 `#print axioms jsp_001021`）：仅 `propext`、`Classical.choice`、
`Quot.sound`。**无 `sorryAx`，未使用 `native_decide`**（全部推理为内核可核查的构造性/经典逻辑）。

## 数学出处（原问题的解答，非本仓库贡献）

- R. Stearns, *The voting problem*, Amer. Math. Monthly 66 (1959), 761–763.
- P. Erdős and L. Moser, *On the representation of directed graphs as unions of orderings*,
  Magyar Tud. Akad. Mat. Kutató Int. Közl. 9 (1964), 125–132.

本仓库的贡献仅为 **Lean 形式化验证**（下界方向；上界 2⌊log₂ n⌋+1 的构造不在本提交范围内）。
按孙宇晨奖公布规则：奖项覆盖自 2026 年 1 月 1 日起取得的数学进展；此前已解但之后完成
形式化验证的，形式化者可获奖。
