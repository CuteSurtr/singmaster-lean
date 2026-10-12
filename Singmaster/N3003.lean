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
# `3003` appears eight times in Pascal's triangle

$$\binom{3003}{1} = \binom{78}{2} = \binom{15}{5} = \binom{14}{6} = 3003,$$
and each of these appears twice by symmetry. `3003` is the only number known to appear eight
times, and no number is known to appear more often.

The proof that there are no other positions: if `C(n, k) = 3003` with `2 ≤ k ≤ n - 2`, then
`C(n, 2) ≤ 3003` by unimodality, so `n ≤ 78`. The rows `n ≤ 78` are checked by the kernel,
which evaluates `C(n, k)` as `n (n - 1) ⋯ (n - k + 1) / k!`.

*Reference:* D. Singmaster, *How often does an integer occur as a binomial coefficient?*,
Amer. Math. Monthly 78 (1971), 385-386.
-/

namespace Singmaster

-- The default `synthInstance.maxSize` is too small for the `Decidable` instance below.
set_option synthInstance.maxSize 1024 in
/-- The rows `n < 79` contain `3003` only at the six positions listed. -/
theorem small_rows_3003 :
    ∀ n < 79, ∀ k < n, 1 ≤ k → n.descFactorial k / k.factorial = 3003 →
      (n, k) ∈ [(78, 2), (78, 76), (15, 5), (15, 10), (14, 6), (14, 8)] := by
  decide +kernel

theorem choose_78_2 : (78 : ℕ).choose 2 = 3003 := by
  norm_num [Nat.choose_two_right]

theorem choose_15_5 : (15 : ℕ).choose 5 = 3003 :=
  (Nat.choose_eq_descFactorial_div_factorial 15 5).trans (by decide +kernel)

theorem choose_14_6 : (14 : ℕ).choose 6 = 3003 :=
  (Nat.choose_eq_descFactorial_div_factorial 14 6).trans (by decide +kernel)

/-- The positions of `3003` in Pascal's triangle with `1 ≤ k < n`. -/
theorem solutions_3003 :
    solutions 3003 =
      {(3003, 1), (3003, 3002), (78, 2), (78, 76), (15, 5), (15, 10), (14, 6), (14, 8)} := by
  ext ⟨n, k⟩
  simp only [mem_solutions, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hk, hkn, h⟩
    by_cases hn : n < 79
    · have := small_rows_3003 n hn k hkn hk
        ((Nat.choose_eq_descFactorial_div_factorial n k).symm.trans h)
      simp only [List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq] at this
      omega
    · rcases (show k = 1 ∨ k + 1 = n ∨ (2 ≤ k ∧ k + 2 ≤ n) by omega) with
        rfl | hk1 | ⟨hk2, hkn2⟩
      · rw [Nat.choose_one_right] at h
        omega
      · rw [Nat.choose_symm_of_eq_add hk1.symm, Nat.choose_one_right] at h
        omega
      · -- Here `3081 = C(79, 2) ≤ C(n, 2) ≤ C(n, k) = 3003`.
        have h1 := choose_le_choose_of_le_of_le_sub hk2 (show k ≤ n - 2 by omega)
        have h2 : (79 : ℕ).choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 (by omega)
        have h3 : (79 : ℕ).choose 2 = 3081 := by norm_num [Nat.choose_two_right]
        omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      refine ⟨by norm_num, by norm_num, ?_⟩
    · exact Nat.choose_one_right 3003
    · exact (Nat.choose_symm_of_eq_add (by norm_num)).trans (Nat.choose_one_right 3003)
    · exact choose_78_2
    · exact (Nat.choose_symm_of_eq_add (by norm_num)).trans choose_78_2
    · exact choose_15_5
    · exact (Nat.choose_symm_of_eq_add (by norm_num)).trans choose_15_5
    · exact choose_14_6
    · exact (Nat.choose_symm_of_eq_add (by norm_num)).trans choose_14_6

/-- **`N(3003) = 8`**: `3003` appears exactly eight times in Pascal's triangle with `1 ≤ k < n`. -/
theorem singmaster.variants.ncard_3003 : (solutions 3003).ncard = 8 := by
  have h : solutions 3003 = ↑({(3003, 1), (3003, 3002), (78, 2), (78, 76), (15, 5), (15, 10),
      (14, 6), (14, 8)} : Finset (ℕ × ℕ)) := by
    rw [solutions_3003]
    simp only [Finset.coe_insert, Finset.coe_singleton]
  rw [h]
  exact (Set.ncard_coe_finset _).trans (by decide)

/-- Any uniform bound in Singmaster's conjecture is at least `8`. -/
theorem eight_le_of_bound {C : ℕ} (hC : ∀ t > 1, (solutions t).ncard ≤ C) : 8 ≤ C := by
  have h := hC 3003 (by norm_num)
  rwa [singmaster.variants.ncard_3003] at h

end Singmaster
