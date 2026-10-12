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
# The Lind–Singmaster family

With `F i = Nat.fib i`, for every `i`
$$\binom{F_{2i+2} F_{2i+3}}{F_{2i} F_{2i+3}} = \binom{F_{2i+2} F_{2i+3} - 1}{F_{2i} F_{2i+3} + 1}.$$
For `i = 1` this is `C(15, 5) = C(14, 6) = 3003`, and for `i = 2` it is `C(104, 39) = C(103, 40)`.
For `i ≥ 1` the common value also appears at `(t, 1)`, `(t, t - 1)` and at the two mirror images,
so infinitely many numbers appear at least six times in Pascal's triangle.

The proof writes `a = F (2i)` and `b = F (2i + 1)`. Cassini's identity at even index gives
`b² = ab + a² + 1`, and this is the only property of the Fibonacci numbers used.

*References:*
- D. A. Lind, *The quadratic field Q(√5) and a certain Diophantine equation*,
  Fibonacci Quart. 6 (1968), 86-93.
- D. Singmaster, *Repeated binomial coefficients and Fibonacci numbers*,
  Fibonacci Quart. 13 (1975), 295-298.
-/

open Nat

namespace Singmaster

/-! ### Collisions between consecutive rows -/

/-- If `n (k + 1) = (n - k)(n - k - 1)` then `C(n, k) = C(n - 1, k + 1)`. Here `n = k + d + 1`,
so the hypothesis reads `(k + d + 1)(k + 1) = (d + 1) d`. -/
theorem choose_eq_choose_pred_succ {k d : ℕ} (h : (k + d + 1) * (k + 1) = (d + 1) * d) :
    (k + d + 1).choose k = (k + d).choose (k + 1) := by
  have ha : (k + d).choose (k + 1) * (k + 1) = (k + d).choose k * d := by
    have := Nat.choose_succ_right_eq (k + d) k
    rwa [Nat.add_sub_cancel_left] at this
  have hb : (k + d + 1) * (k + d).choose k = (k + d + 1).choose (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (k + d) k
  have hc : (k + d + 1).choose (k + 1) * (k + 1) = (k + d + 1).choose k * (d + 1) := by
    have := Nat.choose_succ_right_eq (k + d + 1) k
    rwa [show k + d + 1 - k = d + 1 by omega] at this
  have hpos : 0 < (k + d + 1) * (k + 1) := by positivity
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc (k + d + 1) * (k + 1) * (k + d + 1).choose k
      = d * ((k + d + 1).choose k * (d + 1)) := by rw [h]; ring
    _ = d * ((k + d + 1) * (k + d).choose k) := by rw [← hc, hb]
    _ = (k + d + 1) * ((k + d).choose k * d) := by ring
    _ = (k + d + 1) * (k + 1) * (k + d).choose (k + 1) := by rw [← ha]; ring

/-- The six positions of a value `t = C(n, k) = C(n - 1, k + 1)`. -/
def collisionPositions (n k t : ℕ) : List (ℕ × ℕ) :=
  [(n, k), (n, n - k), (n - 1, k + 1), (n - 1, n - k - 2), (t, 1), (t, t - 1)]

/-- A collision `C(n, k) = C(n - 1, k + 1)` with `2 ≤ k` and `2k + 3 < n` is a number that
appears at least six times in Pascal's triangle. -/
theorem six_le_ncard_of_collision {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k + 3 < n)
    (h : n.choose k = (n - 1).choose (k + 1)) : 6 ≤ (solutions (n.choose k)).ncard := by
  have hnt : n < n.choose k := lt_choose hk (by omega)
  generalize ht : n.choose k = t at h hnt ⊢
  have hnd : (collisionPositions n k t).Nodup := by
    simp only [collisionPositions, List.nodup_cons, List.mem_cons, List.mem_nil_iff, or_false,
      List.nodup_nil, Prod.mk.injEq, not_or, not_and, not_false_eq_true, and_true]
    omega
  have hsub : ((collisionPositions n k t).toFinset : Set (ℕ × ℕ)) ⊆ solutions t := by
    intro p hp
    simp only [collisionPositions, Finset.mem_coe, List.mem_toFinset, List.mem_cons,
      List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [mem_solutions]
    · exact ⟨by omega, by omega, ht⟩
    · exact ⟨by omega, by omega, (Nat.choose_symm (by omega)).trans ht⟩
    · exact ⟨by omega, by omega, h.symm⟩
    · exact ⟨by omega, by omega, (Nat.choose_symm_of_eq_add (by omega)).trans h.symm⟩
    · exact ⟨le_rfl, by omega, Nat.choose_one_right t⟩
    · exact ⟨by omega, by omega,
        (Nat.choose_symm_of_eq_add (by omega)).trans (Nat.choose_one_right t)⟩
  calc 6 = ((collisionPositions n k t).toFinset : Set (ℕ × ℕ)).ncard := by
        rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
        rfl
    _ ≤ (solutions t).ncard := Set.ncard_le_ncard hsub (solutions_finite t)

/-! ### The algebraic core -/

/-- If `b² = ab + a² + 1`, then `n = (a + b)(a + 2b)` and `k = a(a + 2b)` satisfy
`C(n, k) = C(n - 1, k + 1)`. -/
theorem choose_eq_of_cassini {a b : ℕ} (hc : b ^ 2 = a * b + a ^ 2 + 1) :
    ((a + b) * (a + 2 * b)).choose (a * (a + 2 * b)) =
      ((a + b) * (a + 2 * b) - 1).choose (a * (a + 2 * b) + 1) := by
  have hn : (a + b) * (a + 2 * b) = a * (a + 2 * b) + (a + b) ^ 2 + 1 := by nlinarith [hc]
  have hk : a * (a + 2 * b) + 1 = b * (a + b) := by nlinarith [hc]
  have hd : (a + b) ^ 2 + 1 = b * (a + 2 * b) := by nlinarith [hc]
  rw [hn, Nat.add_sub_cancel]
  apply choose_eq_choose_pred_succ
  rw [← hn, hk, hd]
  ring

/-- The size conditions of `six_le_ncard_of_collision`, from `b² = ab + a² + 1` and `1 ≤ a`. -/
theorem cassini_bounds {a b : ℕ} (hc : b ^ 2 = a * b + a ^ 2 + 1) (ha : 1 ≤ a) :
    2 ≤ a * (a + 2 * b) ∧ 2 * (a * (a + 2 * b)) + 3 < (a + b) * (a + 2 * b) := by
  have hab : a + 1 ≤ b := by
    by_contra h
    have h' : b ≤ a := by omega
    nlinarith [Nat.mul_le_mul h' (le_refl b)]
  constructor
  · nlinarith [Nat.mul_le_mul ha (le_refl (a + 2 * b))]
  · nlinarith [Nat.mul_le_mul hab (le_refl (a + 2 * b))]

theorem six_le_ncard_of_cassini {a b : ℕ} (hc : b ^ 2 = a * b + a ^ 2 + 1) (ha : 1 ≤ a) :
    6 ≤ (solutions (((a + b) * (a + 2 * b)).choose (a * (a + 2 * b)))).ncard :=
  six_le_ncard_of_collision (cassini_bounds hc ha).1 (cassini_bounds hc ha).2
    (choose_eq_of_cassini hc)

theorem lt_choose_of_cassini {a b : ℕ} (hc : b ^ 2 = a * b + a ^ 2 + 1) (ha : 1 ≤ a) :
    a < ((a + b) * (a + 2 * b)).choose (a * (a + 2 * b)) := by
  obtain ⟨h1, h2⟩ := cassini_bounds hc ha
  have h3 := lt_choose (n := (a + b) * (a + 2 * b)) h1 (by omega)
  have h4 : a * 1 ≤ a * (a + 2 * b) := Nat.mul_le_mul (le_refl a) (by omega)
  omega

/-! ### Fibonacci numbers -/

theorem fib_two_mul_add_two (i : ℕ) : fib (2 * i + 2) = fib (2 * i) + fib (2 * i + 1) :=
  fib_add_two

theorem fib_two_mul_add_three (i : ℕ) :
    fib (2 * i + 3) = fib (2 * i) + 2 * fib (2 * i + 1) := by
  have h : fib (2 * i + 3) = fib (2 * i + 1) + fib (2 * i + 2) := fib_add_two
  rw [h, fib_two_mul_add_two]
  ring

/-- Cassini's identity at even index: `F(2i+1)² = F(2i) F(2i+1) + F(2i)² + 1`. -/
theorem fib_two_mul_add_one_sq (i : ℕ) :
    fib (2 * i + 1) ^ 2 = fib (2 * i) * fib (2 * i + 1) + fib (2 * i) ^ 2 + 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e2 : fib (2 * (i + 1)) = fib (2 * i) + fib (2 * i + 1) := by
      rw [show 2 * (i + 1) = 2 * i + 2 by ring]
      exact fib_two_mul_add_two i
    have e3 : fib (2 * (i + 1) + 1) = fib (2 * i) + 2 * fib (2 * i + 1) := by
      rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring]
      exact fib_two_mul_add_three i
    rw [e2, e3]
    nlinarith [ih]

theorem one_le_fib_two_mul_add_one (i : ℕ) : 1 ≤ fib (2 * i + 1) := by
  have h := fib_two_mul_add_one_sq i
  by_contra hb
  have h0 : fib (2 * i + 1) = 0 := by omega
  rw [h0] at h
  linarith [Nat.zero_le (fib (2 * i) ^ 2)]

theorem le_fib_two_mul (i : ℕ) : i ≤ fib (2 * i) := by
  induction i with
  | zero => exact Nat.zero_le _
  | succ i ih =>
    have e2 : fib (2 * (i + 1)) = fib (2 * i) + fib (2 * i + 1) := by
      rw [show 2 * (i + 1) = 2 * i + 2 by ring]
      exact fib_two_mul_add_two i
    have := one_le_fib_two_mul_add_one i
    omega

/-! ### The family -/

/-- **The Lind–Singmaster identity.**
`C(F(2i+2) F(2i+3), F(2i) F(2i+3)) = C(F(2i+2) F(2i+3) - 1, F(2i) F(2i+3) + 1)`. -/
theorem choose_fib_eq (i : ℕ) :
    (fib (2 * i + 2) * fib (2 * i + 3)).choose (fib (2 * i) * fib (2 * i + 3)) =
      (fib (2 * i + 2) * fib (2 * i + 3) - 1).choose (fib (2 * i) * fib (2 * i + 3) + 1) := by
  rw [fib_two_mul_add_two, fib_two_mul_add_three]
  exact choose_eq_of_cassini (fib_two_mul_add_one_sq i)

/-- For `i ≥ 1`, the common value of the Lind–Singmaster identity appears at least six times in
Pascal's triangle. -/
theorem six_le_ncard_solutions_fib {i : ℕ} (hi : 1 ≤ i) :
    6 ≤ (solutions
      ((fib (2 * i + 2) * fib (2 * i + 3)).choose (fib (2 * i) * fib (2 * i + 3)))).ncard := by
  rw [fib_two_mul_add_two, fib_two_mul_add_three]
  exact six_le_ncard_of_cassini (fib_two_mul_add_one_sq i) (hi.trans (le_fib_two_mul i))

theorem lt_choose_fib {i : ℕ} (hi : 1 ≤ i) :
    i < (fib (2 * i + 2) * fib (2 * i + 3)).choose (fib (2 * i) * fib (2 * i + 3)) := by
  rw [fib_two_mul_add_two, fib_two_mul_add_three]
  have h1 := lt_choose_of_cassini (fib_two_mul_add_one_sq i) (hi.trans (le_fib_two_mul i))
  have h2 := le_fib_two_mul i
  omega

theorem exists_gt_six_le_ncard (M : ℕ) : ∃ t, M < t ∧ 6 ≤ (solutions t).ncard :=
  ⟨_, by have := lt_choose_fib (i := M + 1) (by omega); omega,
    six_le_ncard_solutions_fib (i := M + 1) (by omega)⟩

/-- **Infinitely many numbers appear at least six times in Pascal's triangle**
(Lind 1968, Singmaster 1975). -/
theorem singmaster.variants.infinite_six_le_ncard :
    {t : ℕ | 6 ≤ (solutions t).ncard}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  obtain ⟨t, hMt, ht⟩ := exists_gt_six_le_ncard M
  have := hM (show t ∈ {t : ℕ | 6 ≤ (solutions t).ncard} from ht)
  omega

end Singmaster
