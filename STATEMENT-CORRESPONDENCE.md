# Statement correspondence — JSP-001021

This document maps each clause of the problem record to the formal statement in
`Jsp001021.lean`, so reviewers can check that the formal theorem *is* the recorded result.

## Problem record (Justin Sun Prize problem bank)

**JSP-001021** — "How large a transitive subtournament must every tournament of prescribed
order contain?" Recorded status: **Solved**; the recorded answer includes the Erdős–Moser
lower bound: *every tournament on n vertices contains a transitive subtournament on at
least log₂ n + 1 vertices* (references: Stearns 1959 [St59]; Erdős–Moser 1964 [ErMo64]).

## Formal statement

```lean
theorem jsp_001021 (n : Nat) (hn : 1 ≤ n) (E : Fin n → Fin n → Bool)
    (hirr : ∀ i, E i i = false)
    (htot : ∀ i j, i ≠ j → E i j = !E j i) :
    ∃ s : List (Fin n), s.Nodup ∧ Nat.log2 n + 1 ≤ s.length ∧
      ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, E a b = true → E b c = true → E a c = true
```

## Clause-by-clause correspondence

| Problem-record clause | Formal counterpart | Notes |
| --- | --- | --- |
| "every tournament" | `E : Fin n → Fin n → Bool` with `hirr`, `htot` | `hirr`: no loops. `htot`: for i ≠ j exactly one of `E i j`, `E j i` holds (asymmetry + totality), the standard definition of a tournament on n labeled vertices. Quantification is over *all* such `E`, i.e. all tournaments up to isomorphism. |
| "on n vertices" | `n : Nat`, `hn : 1 ≤ n`, vertex type `Fin n` | The degenerate case n = 0 is excluded (the bound ⌊log₂ 0⌋ + 1 = 1 would be false for the empty tournament). |
| "contains a transitive subtournament" | `∃ s : List (Fin n), s.Nodup ∧ (∀ a b c ∈ s, E a b → E b c → E a c)` | A subtournament is determined by a subset of vertices (here: a duplicate-free list). Transitivity of the induced subtournament is exactly the displayed implication; combined with `htot` this makes `s` linearly ordered by `E`. |
| "on at least log₂ n + 1 vertices" | `Nat.log2 n + 1 ≤ s.length` | `Nat.log2 n = ⌊log₂ n⌋` for n ≥ 1 (Lean core definition). The real-valued reading "≥ log₂ n + 1" and the integer-valued record coincide on integer cardinalities. |

## Scope

- **Included:** the lower bound (universal direction) — the literal answer to "how large a
  transitive subtournament *must* every tournament contain?".
- **Not included:** the Erdős–Moser upper bound (existence of tournaments whose largest
  transitive subtournament has at most 2⌊log₂ n⌋ + 1 vertices). This submission makes no
  claim about that direction.

## Verification

- Toolchain: Lean v4.34.0 (`lean-toolchain`), **Lean 4 core only — no Mathlib**.
- Kernel check: `lean Jsp001021.lean` completes with no errors.
- Axiom audit: `#print axioms jsp_001021` prints only `propext`, `Classical.choice`,
  `Quot.sound`. No `sorryAx`; no `native_decide`/`Lean.ofReduceBool` trusted computation.
