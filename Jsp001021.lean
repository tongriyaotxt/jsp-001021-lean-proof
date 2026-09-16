/-!
# JSP-001021 — Transitive subtournament lower bound (Stearns–Erdős–Moser)

Every tournament on `n ≥ 1` vertices contains a transitive subtournament on at
least `⌊log₂ n⌋ + 1` vertices.

Mathematical references (the result itself is classical, not new here):
- R. Stearns, *The voting problem*, Amer. Math. Monthly 66 (1959), 761–763.
- P. Erdős and L. Moser, *On the representation of directed graphs as unions of
  orderings*, Magyar Tud. Akad. Mat. Kutató Int. Közl. 9 (1964), 125–132.

This file is a self-contained formalization in **Lean 4 core** (no Mathlib).
The proof is the classical induction: some vertex has outdegree at least
`(n-1)/2`; apply the induction hypothesis inside its out-neighborhood and
prepend the vertex.
-/

namespace Jsp001021

/-! ## List weighted-sum utilities -/

/-- Sum of `f` over a list. -/
def ssum (l : List α) (f : α → Nat) : Nat := (l.map f).sum

theorem ssum_nil (f : α → Nat) : ssum [] f = 0 := rfl

theorem ssum_cons (a : α) (l : List α) (f : α → Nat) :
    ssum (a :: l) f = f a + ssum l f := by simp [ssum]

theorem ssum_congr {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x = g x) :
    ssum l f = ssum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons, ssum_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem ssum_add (l : List α) (f g : α → Nat) :
    ssum l (fun x => f x + g x) = ssum l f + ssum l g := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [ssum_cons, ssum_cons, ssum_cons, ih]; omega

theorem ssum_two (l : List α) (f : α → Nat) :
    2 * ssum l f = ssum l (fun x => 2 * f x) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [ssum_cons, ssum_cons, ← ih]; omega

theorem ssum_const (l : List α) (c : Nat) :
    ssum l (fun _ => c) = c * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons, ih, List.length_cons, Nat.mul_succ]
    omega

theorem ssum_le {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    ssum l f ≤ ssum l g := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    rw [ssum_cons, ssum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..))
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem ssum_swap (A : List α) (B : List β) (f : α → β → Nat) :
    ssum A (fun i => ssum B (f i)) = ssum B (fun j => ssum A (fun i => f i j)) := by
  induction A with
  | nil =>
    have hz : ssum B (fun j => ssum [] (fun i => f i j)) = 0 := by
      calc ssum B (fun j => ssum [] (fun i => f i j))
          = ssum B (fun _ => 0) := ssum_congr (fun j _ => rfl)
        _ = 0 * B.length := ssum_const B 0
        _ = 0 := Nat.zero_mul _
    rw [ssum_nil]; exact hz.symm
  | cons a A ih =>
    rw [ssum_cons]
    have step : ∀ j ∈ B, ssum (a :: A) (fun i => f i j) =
        f a j + ssum A (fun i => f i j) := fun j _ => ssum_cons a A _
    calc ssum B (f a) + ssum A (fun i => ssum B (f i))
        = ssum B (f a) + ssum B (fun j => ssum A (fun i => f i j)) := by rw [ih]
      _ = ssum B (fun j => f a j + ssum A (fun i => f i j)) := (ssum_add B (f a) _).symm
      _ = ssum B (fun j => ssum (a :: A) (fun i => f i j)) := (ssum_congr step).symm

/-- In a duplicate-free list containing `x`, counting "1 everywhere except at `x`"
gives `length - 1`. -/
theorem ssum_ite_eq_of_nodup [DecidableEq α] (x : α) :
    ∀ (l : List α), l.Nodup → x ∈ l →
      ssum l (fun y => if x = y then 0 else 1) = l.length - 1 := by
  intro l
  induction l with
  | nil => intro _ hx; simp at hx
  | cons a l ih =>
    intro nd hx
    rw [List.nodup_cons] at nd
    rw [List.mem_cons] at hx
    cases hx with
    | inl h =>
      subst h
      rw [ssum_cons]
      have hall : ssum l (fun y => if x = y then 0 else 1) = l.length := by
        calc ssum l (fun y => if x = y then 0 else 1)
            = ssum l (fun _ => 1) := by
              apply ssum_congr
              intro y hy
              have hne : x ≠ y := by
                intro hxy; subst hxy; exact nd.1 hy
              simp [hne]
          _ = 1 * l.length := ssum_const l 1
          _ = l.length := Nat.one_mul _
      rw [hall]
      simp
    | inr h =>
      rw [ssum_cons]
      have hne : ¬ x = a := by
        intro hxa; subst hxa; exact nd.1 h
      have h0 : (if x = a then 0 else 1) = 1 := by simp [hne]
      rw [h0, ih nd.2 h]
      have hpos : 0 < l.length := by
        cases l with
        | nil => simp at h
        | cons b bs => simp
      rw [List.length_cons]
      omega

/-- Length of a filter as a weighted sum. -/
theorem filter_length_eq (p : α → Bool) (l : List α) :
    (l.filter p).length = ssum l (fun x => (p x).toNat) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a <;> simp [List.filter, hp, ssum_cons] <;> omega

/-- Filter lengths of a predicate and its negation add up to the list length. -/
theorem filter_length_add (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a <;> simp [List.filter, hp, List.length_cons] <;> omega

/-- Mapping a duplicate-free list by an injective function keeps it duplicate-free. -/
theorem nodup_map_of_injective {f : α → β} (hf : Function.Injective f) :
    ∀ {l : List α}, l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a l ih =>
    intro h
    rw [List.nodup_cons] at h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih h.2⟩
    intro hmem
    rw [List.mem_map] at hmem
    cases hmem with
    | intro b hb =>
      cases hb with
      | intro hb hfb =>
        have := hf hfb
        subst this
        exact h.1 hb

/-- In a duplicate-free list, `get` is injective. -/
theorem get_injective_of_nodup {l : List α} (nd : l.Nodup) :
    Function.Injective l.get := by
  intro a b h
  rw [List.get_eq_getElem, List.get_eq_getElem] at h
  exact Fin.ext (nd.getElem_inj.mp h)

/-! ## Tournaments -/

/-- Pigeonhole: in every tournament on `n ≥ 2` vertices some vertex has
outdegree at least `(n-1)/2`, stated as `n - 1 ≤ 2 * outdeg v`. -/
theorem exists_high_outdeg {n : Nat} (hn : 2 ≤ n) (E : Fin n → Fin n → Bool)
    (hirr : ∀ i, E i i = false) (htot : ∀ i j, i ≠ j → E i j = !E j i) :
    ∃ v : Fin n, n - 1 ≤ 2 * ssum (List.finRange n) (fun j => (E v j).toNat) := by
  by_cases hex : ∃ v : Fin n, n - 1 ≤ 2 * ssum (List.finRange n) (fun j => (E v j).toNat)
  · exact hex
  · exfalso
    -- Otherwise every outdegree is strictly below (n-1)/2.
    have h : ∀ v : Fin n, 2 * ssum (List.finRange n) (fun j => (E v j).toNat) < n - 1 := by
      intro v
      by_cases hv2 : n - 1 ≤ 2 * ssum (List.finRange n) (fun j => (E v j).toNat)
      · exact absurd ⟨v, hv2⟩ hex
      · omega
    -- Every ordered off-diagonal pair contributes exactly one to the double count.
    have hpt : ∀ i ∈ List.finRange n, ∀ j ∈ List.finRange n,
        (E i j).toNat + (E j i).toNat = if i = j then 0 else 1 := by
      intro i _ j _
      by_cases hjj : i = j
      · subst hjj; simp [hirr]
      · have h2 := htot i j hjj
        cases h1 : E j i
        · rw [h1] at h2; simp [h2, hjj]
        · rw [h1] at h2; simp [h2, hjj]
    -- Each vertex contributes exactly n - 1 to the double count.
    have hw : ∀ i ∈ List.finRange n,
        ssum (List.finRange n) (fun j => (E i j).toNat + (E j i).toNat) = n - 1 := by
      intro i hi
      calc ssum (List.finRange n) (fun j => (E i j).toNat + (E j i).toNat)
          = ssum (List.finRange n) (fun j => if i = j then 0 else 1) :=
            ssum_congr (fun j hj => hpt i hi j hj)
        _ = (List.finRange n).length - 1 :=
            ssum_ite_eq_of_nodup i _ (List.nodup_finRange n) (List.mem_finRange i)
        _ = n - 1 := by rw [List.length_finRange]
    -- The doubled total outdegree sum equals n * (n - 1).
    have e2 : ssum (List.finRange n) (fun i => ssum (List.finRange n) (fun j => (E i j).toNat))
            + ssum (List.finRange n)
                (fun i => ssum (List.finRange n) (fun j => (E j i).toNat))
          = ssum (List.finRange n)
              (fun i => ssum (List.finRange n) (fun j => (E i j).toNat + (E j i).toNat)) := by
      rw [← ssum_add]
      exact ssum_congr (fun i _ => (ssum_add _ _ _).symm)
    have e3 : ssum (List.finRange n)
            (fun i => ssum (List.finRange n) (fun j => (E j i).toNat))
          = ssum (List.finRange n) (fun i => ssum (List.finRange n) (fun j => (E i j).toNat)) :=
      ssum_swap (List.finRange n) (List.finRange n) (fun i j => (E j i).toNat)
    have e1 : ssum (List.finRange n)
            (fun i => ssum (List.finRange n) (fun j => (E i j).toNat + (E j i).toNat))
          = ssum (List.finRange n) (fun _ => n - 1) := ssum_congr hw
    have hsum : 2 * ssum (List.finRange n) (fun i => ssum (List.finRange n) (fun j => (E i j).toNat))
          = n * (n - 1) := by
      calc 2 * ssum (List.finRange n) (fun i => ssum (List.finRange n) (fun j => (E i j).toNat))
          = ssum (List.finRange n) (fun i => ssum (List.finRange n) (fun j => (E i j).toNat))
            + ssum (List.finRange n) (fun i => ssum (List.finRange n) (fun j => (E i j).toNat)) := by
              omega
        _ = ssum (List.finRange n) (fun i => ssum (List.finRange n) (fun j => (E i j).toNat))
            + ssum (List.finRange n) (fun i => ssum (List.finRange n) (fun j => (E j i).toNat)) :=
              congrArg _ e3.symm
        _ = ssum (List.finRange n)
              (fun i => ssum (List.finRange n) (fun j => (E i j).toNat + (E j i).toNat)) :=
              e2
        _ = ssum (List.finRange n) (fun _ => n - 1) := e1
        _ = (n - 1) * n := by rw [ssum_const, List.length_finRange]
        _ = n * (n - 1) := Nat.mul_comm _ _
    -- But with all outdegrees small the doubled sum is at most n * (n - 2).
    have hbound : 2 * ssum (List.finRange n) (fun i => ssum (List.finRange n) (fun j => (E i j).toNat))
          ≤ n * (n - 2) := by
      calc 2 * ssum (List.finRange n) (fun i => ssum (List.finRange n) (fun j => (E i j).toNat))
          = ssum (List.finRange n)
              (fun i => 2 * ssum (List.finRange n) (fun j => (E i j).toNat)) :=
              ssum_two _ _
        _ ≤ ssum (List.finRange n) (fun _ => n - 2) :=
              ssum_le (fun i _ => by have := h i; omega)
        _ = (n - 2) * n := by rw [ssum_const, List.length_finRange]
        _ = n * (n - 2) := Nat.mul_comm _ _
    have hlt : n * (n - 2) < n * (n - 1) :=
      (Nat.mul_lt_mul_left (by omega : 0 < n)).mpr (by omega : n - 2 < n - 1)
    omega

/-! ## The main induction -/

theorem jsp_001021_aux : ∀ n : Nat, 1 ≤ n → ∀ (E : Fin n → Fin n → Bool),
    (∀ i, E i i = false) → (∀ i j, i ≠ j → E i j = !E j i) →
    ∃ s : List (Fin n), s.Nodup ∧ Nat.log2 n + 1 ≤ s.length ∧
      ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, E a b = true → E b c = true → E a c = true := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn E hirr htot
    by_cases h1 : n = 1
    · -- Base case: the single vertex is a transitive subtournament of size 1.
      subst h1
      refine ⟨[⟨0, by decide⟩], by decide, by decide, ?_⟩
      intro a ha b hb c hc hab hbc
      rw [List.mem_singleton] at ha hb hc
      subst ha; subst hb; subst hc
      rw [hirr] at hab
      exact Bool.noConfusion hab
    · -- Inductive step: n ≥ 2.
      have hn2 : 2 ≤ n := by omega
      cases exists_high_outdeg hn2 E hirr htot with
      | intro v hv =>
        -- The out-neighborhood of `v`, as a fresh variable L.
        generalize hL : (List.finRange n).filter (E v) = L
        have hndL : L.Nodup := hL ▸ List.Pairwise.filter _ (List.nodup_finRange n)
        have hLenL : L.length = ssum (List.finRange n) (fun j => (E v j).toNat) :=
          hL ▸ filter_length_eq _ _
        have memL : ∀ a : Fin L.length, E v (L.get a) = true := by
          intro a
          have hmem : L.get a ∈ (List.finRange n).filter (E v) := hL.symm ▸ List.get_mem L a
          exact (List.mem_filter.mp hmem).2
        have hm1 : 1 ≤ L.length := by rw [← hLenL] at hv; omega
        have hmn : L.length < n := by
          have hadd := filter_length_add (E v) (List.finRange n)
          rw [List.length_finRange, hL] at hadd
          have hvcompl : v ∈ (List.finRange n).filter (fun j => !(E v j)) := by
            rw [List.mem_filter]
            exact ⟨List.mem_finRange v, by simp [hirr v]⟩
          have hpos : 1 ≤ ((List.finRange n).filter (fun j => !(E v j))).length := by
            cases hcl : (List.finRange n).filter (fun j => !(E v j)) with
            | nil => rw [hcl] at hvcompl; simp at hvcompl
            | cons b bs => simp
          omega
        -- The subtournament on the out-neighborhood.
        have hirr' : ∀ a : Fin L.length, E (L.get a) (L.get a) = false := fun a => hirr _
        have htot' : ∀ a b : Fin L.length, a ≠ b →
            E (L.get a) (L.get b) = !E (L.get b) (L.get a) := by
          intro a b hab
          exact htot _ _ (fun heq => hab (get_injective_of_nodup hndL heq))
        cases ih L.length hmn hm1 (fun a b => E (L.get a) (L.get b)) hirr' htot' with
        | intro s' hs' =>
          -- Prepend `v` to the transitive subtournament of the out-neighborhood.
          refine ⟨v :: s'.map L.get, ?_, ?_, ?_⟩
          · rw [List.nodup_cons]
            constructor
            · intro hmem
              rw [List.mem_map] at hmem
              cases hmem with
              | intro a ha =>
                cases ha with
                | intro _ hga =>
                  have h1 : E v (L.get a) = true := memL a
                  rw [hga, hirr] at h1
                  exact Bool.noConfusion h1
            · exact nodup_map_of_injective (get_injective_of_nodup hndL) hs'.1
          · rw [List.length_cons, List.length_map]
            have hlog : Nat.log2 n ≤ Nat.log2 L.length + 1 := by
              have hn0 : n ≠ 0 := by omega
              have hm0 : L.length ≠ 0 := by omega
              have hk : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn0).mp (Nat.le_refl _)
              have hk1 : 1 ≤ Nat.log2 n := (Nat.le_log2 hn0).mpr (by omega)
              have hpow : 2 ^ Nat.log2 n = 2 ^ (Nat.log2 n - 1) * 2 := by
                have hk2 : Nat.log2 n = (Nat.log2 n - 1) + 1 := (Nat.sub_add_cancel hk1).symm
                calc 2 ^ Nat.log2 n = 2 ^ ((Nat.log2 n - 1) + 1) := congrArg (2 ^ ·) hk2
                  _ = 2 ^ (Nat.log2 n - 1) * 2 := Nat.pow_succ _ _
              have hnm : n ≤ 2 * L.length + 1 := by rw [← hLenL] at hv; omega
              have hkm : 2 ^ (Nat.log2 n - 1) ≤ L.length := by omega
              have hle := (Nat.le_log2 hm0).mpr hkm
              omega
            omega
          · intro a ha b hb c hc hab hbc
            rw [List.mem_cons] at ha hb hc
            cases hb with
            | inl hbv =>
              -- b = v is impossible: nothing in the out-neighborhood maps into v,
              -- and v does not beat itself.
              rw [hbv] at hab
              cases ha with
              | inl hav =>
                rw [hav] at hab
                rw [hirr] at hab
                exact Bool.noConfusion hab
              | inr hat =>
                rw [List.mem_map] at hat
                cases hat with
                | intro a' ha' =>
                  cases ha' with
                  | intro ha's hga' =>
                    have h1 : E v (L.get a') = true := memL a'
                    have hne : v ≠ L.get a' := by
                      intro h; rw [h, hirr] at h1; exact Bool.noConfusion h1
                    have h2 : E (L.get a') v = false := by
                      have ht := htot v (L.get a') hne
                      rw [h1] at ht
                      cases hx : E (L.get a') v with
                      | false => rfl
                      | true => rw [hx] at ht; simp at ht
                    rw [← hga'] at hab
                    rw [h2] at hab
                    exact Bool.noConfusion hab
            | inr hbt =>
              rw [List.mem_map] at hbt
              cases hbt with
              | intro b' hb' =>
                cases hb' with
                | intro hb's hgb' =>
                  cases hc with
                  | inl hcv =>
                    -- c = v is impossible since b = L.get b' loses to v.
                    have h1 : E v (L.get b') = true := memL b'
                    have hne : v ≠ L.get b' := by
                      intro h; rw [h, hirr] at h1; exact Bool.noConfusion h1
                    have h2 : E (L.get b') v = false := by
                      have ht := htot v (L.get b') hne
                      rw [h1] at ht
                      cases hx : E (L.get b') v with
                      | false => rfl
                      | true => rw [hx] at ht; simp at ht
                    rw [hcv, ← hgb'] at hbc
                    rw [h2] at hbc
                    exact Bool.noConfusion hbc
                  | inr hct =>
                    rw [List.mem_map] at hct
                    cases hct with
                    | intro c' hc' =>
                      cases hc' with
                      | intro hc's hgc' =>
                        cases ha with
                        | inl hav =>
                          -- v beats every vertex of the out-neighborhood.
                          rw [hav, ← hgc']
                          exact memL c'
                        | inr hat =>
                          rw [List.mem_map] at hat
                          cases hat with
                          | intro a' ha' =>
                            cases ha' with
                            | intro ha's hga' =>
                              have ht := hs'.2.2 a' ha's b' hb's c' hc's
                              rw [← hga', ← hgb'] at hab
                              rw [← hgb', ← hgc'] at hbc
                              rw [← hga', ← hgc']
                              exact ht hab hbc

/-- **JSP-001021 (formalization of the Stearns–Erdős–Moser lower bound).**
Every tournament on `n` vertices contains a transitive subtournament on at least
`⌊log₂ n⌋ + 1` vertices. -/
theorem jsp_001021 (n : Nat) (hn : 1 ≤ n) (E : Fin n → Fin n → Bool)
    (hirr : ∀ i, E i i = false)
    (htot : ∀ i j, i ≠ j → E i j = !E j i) :
    ∃ s : List (Fin n), s.Nodup ∧ Nat.log2 n + 1 ≤ s.length ∧
      ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, E a b = true → E b c = true → E a c = true :=
  jsp_001021_aux n hn E hirr htot

#print axioms jsp_001021

end Jsp001021
