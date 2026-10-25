/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import Singmaster.Basic

/-!
# Singmaster's bound `N(t) ≤ 2 log₂ t`

Singmaster (1971) proved `N(t) = O(log t)`. In explicit form: fold each position `(n, k)` onto
`j = min(k, n - k)`, remembering which half of the row it came from. For fixed `j ≥ 1` the entries
`C(n, j)` strictly increase with `n`, so each pair `(j, side)` comes from at most one position.
Moreover `2 ^ j ≤ C(2j, j) ≤ C(n, j) = t`, so `j ≤ log₂ t`.

*Reference:* D. Singmaster, *How often does an integer occur as a binomial coefficient?*,
Amer. Math. Monthly 78 (1971), 385-386.
-/

namespace Singmaster

/-- `2 ^ j ≤ C(2j, j)`. -/
theorem two_pow_le_centralBinom (j : ℕ) : 2 ^ j ≤ Nat.centralBinom j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := Nat.succ_mul_centralBinom_succ j
    have h1 := Nat.mul_le_mul (le_refl (2 * (j + 1))) ih
    have h2 := Nat.mul_le_mul (show 2 * (j + 1) ≤ 2 * (2 * j + 1) by omega)
      (le_refl (Nat.centralBinom j))
    have h3 : (j + 1) * 2 ^ (j + 1) ≤ (j + 1) * Nat.centralBinom (j + 1) := by
      rw [h, pow_succ]
      nlinarith [h1, h2]
    exact Nat.le_of_mul_le_mul_left h3 (Nat.succ_pos j)

/-- For `1 ≤ j`, the entries `C(n, j)` with `j ≤ n` strictly increase with `n`. -/
theorem choose_lt_choose_of_lt {j n n' : ℕ} (hj : 1 ≤ j) (hn : j ≤ n) (h : n < n') :
    n.choose j < n'.choose j := by
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have h1 : (n + 1).choose (i + 1) = n.choose i + n.choose (i + 1) := Nat.choose_succ_succ' n i
  have h2 : 0 < n.choose i := Nat.choose_pos (by omega)
  have h3 : (n + 1).choose (i + 1) ≤ n'.choose (i + 1) :=
    Nat.choose_le_choose (i + 1) (Nat.succ_le_of_lt h)
  omega

/-- The position `(n, k)` folded onto the left half of row `n`, together with the half
(`0` for left, `1` for right) it came from. -/
def fold (p : ℕ × ℕ) : ℕ × ℕ := (min p.2 (p.1 - p.2), if 2 * p.2 ≤ p.1 then 0 else 1)

theorem fold_of_mem {t n k : ℕ} (hp : (n, k) ∈ solutions t) :
    1 ≤ min k (n - k) ∧ 2 * min k (n - k) ≤ n ∧ n.choose (min k (n - k)) = t := by
  obtain ⟨hk, hkn, h⟩ := mem_solutions.1 hp
  have h1 := min_le_left k (n - k)
  have h2 := min_le_right k (n - k)
  refine ⟨le_min hk (by omega), by omega, ?_⟩
  rcases le_total k (n - k) with hle | hle
  · rw [min_eq_left hle]
    exact h
  · rw [min_eq_right hle, Nat.choose_symm hkn.le]
    exact h

/-- **Singmaster (1971).** A number `t` appears at most `2 log₂ t` times in Pascal's triangle
with `1 ≤ k < n`. -/
theorem singmaster.variants.ncard_le_two_mul_log (t : ℕ) :
    (solutions t).ncard ≤ 2 * Nat.log 2 t := by
  have hmaps : ∀ p ∈ solutions t,
      fold p ∈ (↑(Finset.Icc 1 (Nat.log 2 t) ×ˢ Finset.range 2) : Set (ℕ × ℕ)) := by
    rintro ⟨n, k⟩ hp
    obtain ⟨h1, h2, h3⟩ := fold_of_mem hp
    simp only [fold, Finset.mem_coe, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
    refine ⟨⟨h1, Nat.le_log_of_pow_le (by norm_num) ?_⟩, by split <;> omega⟩
    calc 2 ^ min k (n - k) ≤ Nat.centralBinom (min k (n - k)) := two_pow_le_centralBinom _
      _ = (2 * min k (n - k)).choose (min k (n - k)) := Nat.centralBinom_eq_two_mul_choose _
      _ ≤ n.choose (min k (n - k)) := Nat.choose_le_choose _ h2
      _ = t := h3
  have hinj : Set.InjOn fold (solutions t) := by
    rintro ⟨n, k⟩ hp ⟨n', k'⟩ hp' hf
    obtain ⟨h1, h2, h3⟩ := fold_of_mem hp
    obtain ⟨-, h2', h3'⟩ := fold_of_mem hp'
    have hk := (mem_solutions.1 hp).2.1
    have hk' := (mem_solutions.1 hp').2.1
    simp only [fold, Prod.mk.injEq] at hf
    obtain ⟨hj, hb⟩ := hf
    rw [hj] at h1 h2 h3
    have hn : n = n' := by
      rcases lt_trichotomy n n' with hlt | heq | hgt
      · have := choose_lt_choose_of_lt h1 (by omega) hlt
        omega
      · exact heq
      · have := choose_lt_choose_of_lt h1 (by omega) hgt
        omega
    subst hn
    have : k = k' := by
      rw [min_def, min_def] at hj
      split_ifs at hj hb <;> omega
    rw [this]
  calc (solutions t).ncard
      ≤ (↑(Finset.Icc 1 (Nat.log 2 t) ×ˢ Finset.range 2) : Set (ℕ × ℕ)).ncard :=
        Set.ncard_le_ncard_of_injOn fold hmaps hinj
    _ = 2 * Nat.log 2 t := by
        rw [Set.ncard_coe_finset, Finset.card_product, Nat.card_Icc, Finset.card_range]
        omega

end Singmaster
