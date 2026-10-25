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
# Certified multiplicities

To find every position of a number `t ≥ 2` it is enough to find its positions `(n, k)` with
`2 ≤ k` and `2k ≤ n`. The other positions are `(t, 1)`, `(t, t - 1)` and the mirror images
`(n, n - k)`.

Column `k` of Pascal's triangle increases with `n`. So a number `a` with
`C(a, k) < t < C(a + 1, k)` certifies that `t` is not in column `k`, and a number `a` with
`C(a, k) < t < C(a + 2, k)` certifies that row `a + 1` is the only candidate. A column `k` with
`C(2k, k) > t` cannot contain `t` at a position with `2k ≤ n`, because `C(n, k) ≥ C(2k, k)` there.

`colsOK` checks such certificates for the columns `2, 3, …` in turn. It compares `k! t` with
`a (a - 1) ⋯ (a - k + 1) = k! C(a, k)` and uses `(a + 1 - k) C(a + 1, k) = (a + 1) C(a, k)` for
the next rows, so it needs no division. `certOK` adds the remaining checks, and
`ncard_eq_of_certOK` turns a successful check into the exact value of `(solutions t).ncard`.
The kernel runs the check with `decide +kernel`, which adds no axiom.
-/

namespace Singmaster

/-! ### One column -/

theorem choose_lt_of_descFactorial_lt {t k a : ℕ} (h : a.descFactorial k < k.factorial * t) :
    a.choose k < t := by
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  exact Nat.lt_of_mul_lt_mul_left h

theorem lt_choose_succ_of_lt {t k a : ℕ}
    (h : k.factorial * t * (a + 1 - k) < (a + 1) * a.descFactorial k) :
    t < (a + 1).choose k := by
  have e : a.choose k * (a + 1) = (a + 1).choose k * (a + 1 - k) := Nat.choose_mul_succ_eq a k
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have h2 : k.factorial * t * (a + 1 - k) < k.factorial * (a + 1).choose k * (a + 1 - k) :=
    calc k.factorial * t * (a + 1 - k) < (a + 1) * (k.factorial * a.choose k) := h
      _ = k.factorial * (a.choose k * (a + 1)) := by ring
      _ = k.factorial * ((a + 1).choose k * (a + 1 - k)) := by rw [e]
      _ = k.factorial * (a + 1).choose k * (a + 1 - k) := by ring
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_mul_lt_mul_right h2)

theorem lt_choose_add_two_of_lt {t k a : ℕ}
    (h : k.factorial * t * ((a + 1 - k) * (a + 2 - k)) <
      (a + 2) * (a + 1) * a.descFactorial k) :
    t < (a + 2).choose k := by
  have e1 : a.choose k * (a + 1) = (a + 1).choose k * (a + 1 - k) := Nat.choose_mul_succ_eq a k
  have e2 : (a + 1).choose k * (a + 2) = (a + 2).choose k * (a + 2 - k) :=
    Nat.choose_mul_succ_eq (a + 1) k
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have h2 : k.factorial * t * ((a + 1 - k) * (a + 2 - k)) <
      k.factorial * (a + 2).choose k * ((a + 1 - k) * (a + 2 - k)) :=
    calc k.factorial * t * ((a + 1 - k) * (a + 2 - k))
        < (a + 2) * (a + 1) * (k.factorial * a.choose k) := h
      _ = k.factorial * (a + 2) * (a.choose k * (a + 1)) := by ring
      _ = k.factorial * (a + 2) * ((a + 1).choose k * (a + 1 - k)) := by rw [e1]
      _ = k.factorial * ((a + 1).choose k * (a + 2)) * (a + 1 - k) := by ring
      _ = k.factorial * ((a + 2).choose k * (a + 2 - k)) * (a + 1 - k) := by rw [e2]
      _ = k.factorial * (a + 2).choose k * ((a + 1 - k) * (a + 2 - k)) := by ring
  exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_mul_lt_mul_right h2)

/-- The certificate `a` for column `k`: `C(a, k) < t`, and `t < C(a + 2, k)` if `(a + 1, k)` is
in `S`, `t < C(a + 1, k)` otherwise. -/
def colOK (t : ℕ) (S : List (ℕ × ℕ)) (k a : ℕ) : Bool :=
  decide (a.descFactorial k < k.factorial * t) &&
    if (a + 1, k) ∈ S then
      decide (k.factorial * t * ((a + 1 - k) * (a + 2 - k)) <
        (a + 2) * (a + 1) * a.descFactorial k)
    else
      decide (k.factorial * t * (a + 1 - k) < (a + 1) * a.descFactorial k)

theorem colOK_sound {t : ℕ} {S : List (ℕ × ℕ)} {k a : ℕ} (h : colOK t S k a = true) {n : ℕ}
    (hn : n.choose k = t) : (n, k) ∈ S := by
  unfold colOK at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have hlo := choose_lt_of_descFactorial_lt h1
  have han : a < n := by
    by_contra hc
    have := Nat.choose_le_choose k (show n ≤ a by omega)
    omega
  split at h2
  · rename_i hS
    have hhi := lt_choose_add_two_of_lt (of_decide_eq_true h2)
    have hn2 : n < a + 2 := by
      by_contra hc
      have := Nat.choose_le_choose k (show a + 2 ≤ n by omega)
      omega
    obtain rfl : n = a + 1 := by omega
    exact hS
  · have hhi := lt_choose_succ_of_lt (of_decide_eq_true h2)
    have := Nat.choose_le_choose k (show a + 1 ≤ n by omega)
    omega

/-! ### All columns -/

/-- The certificates `as` for the columns `k₀, k₀ + 1, …, k₀ + as.length - 1`. -/
def colsOK (t : ℕ) (S : List (ℕ × ℕ)) : ℕ → List ℕ → Bool
  | _, [] => true
  | k, a :: as => colOK t S k a && colsOK t S (k + 1) as

theorem colsOK_sound {t : ℕ} {S : List (ℕ × ℕ)} (as : List ℕ) :
    ∀ k₀, colsOK t S k₀ as = true → ∀ n k, k₀ ≤ k → k < k₀ + as.length →
      n.choose k = t → (n, k) ∈ S := by
  induction as with
  | nil =>
    intro k₀ _ n k h1 h2 _
    simp only [List.length_nil, Nat.add_zero] at h2
    omega
  | cons a as ih =>
    intro k₀ h n k h1 h2 hn
    simp only [colsOK, Bool.and_eq_true] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · exact colOK_sound h.1 hn
    · simp only [List.length_cons] at h2
      exact ih (k₀ + 1) h.2 n k (by omega) (by omega) hn

/-- If the certificates cover the columns `2, …, K - 1` with `K = as.length + 2` and
`C(2K, K) > t`, then every position `(n, k)` of `t` with `2 ≤ k` and `2k ≤ n` is in `S`. -/
theorem mem_of_colsOK {t : ℕ} {S : List (ℕ × ℕ)} {as : List ℕ}
    (hcols : colsOK t S 2 as = true)
    (htop : t < (2 * (as.length + 2)).choose (as.length + 2))
    {n k : ℕ} (hk : 2 ≤ k) (hkn : 2 * k ≤ n) (h : n.choose k = t) : (n, k) ∈ S := by
  by_cases hK : k < as.length + 2
  · exact colsOK_sound as 2 hcols n k hk (by omega) h
  · exfalso
    have h1 : n.choose (as.length + 2) ≤ n.choose k :=
      choose_le_choose_of_le_of_two_mul_le (by omega) hkn
    have h2 : (2 * (as.length + 2)).choose (as.length + 2) ≤ n.choose (as.length + 2) :=
      Nat.choose_le_choose _ (by omega)
    omega

/-! ### All positions -/

/-- All positions of `t`, given its positions `S` with `2 ≤ k` and `2k ≤ n`. -/
def positions (t : ℕ) (S : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (t, 1) :: (t, t - 1) :: (S ++ S.map fun p => (p.1, p.1 - p.2))

/-- Each `(n, k) ∈ S` has `2 ≤ k`, `2k ≤ n` and `C(n, k) = t`, the last checked as
`n (n - 1) ⋯ (n - k + 1) = k! t`. -/
def validHalf (t : ℕ) (S : List (ℕ × ℕ)) : Bool :=
  S.all fun p => decide (2 ≤ p.2) && decide (2 * p.2 ≤ p.1) &&
    decide (p.1.descFactorial p.2 = p.2.factorial * t)

theorem validHalf_sound {t : ℕ} {S : List (ℕ × ℕ)} (h : validHalf t S = true) {p : ℕ × ℕ}
    (hp : p ∈ S) : 2 ≤ p.2 ∧ 2 * p.2 ≤ p.1 ∧ p.1.choose p.2 = t := by
  have h' := List.all_eq_true.1 h p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h'
  refine ⟨h1, h2, ?_⟩
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h3
  exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos _) h3

/-- **Certified positions.** If the checks pass, the positions of `t` are exactly
`positions t S`. -/
theorem solutions_eq_of_check {t : ℕ} {S : List (ℕ × ℕ)} {as : List ℕ} (ht : 2 ≤ t)
    (hS : validHalf t S = true) (hcols : colsOK t S 2 as = true)
    (htop : t < (2 * (as.length + 2)).choose (as.length + 2)) :
    solutions t = {p | p ∈ positions t S} := by
  ext ⟨n, k⟩
  rw [mem_solutions]
  change _ ↔ (n, k) ∈ positions t S
  simp only [positions, List.mem_cons, List.mem_append, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨hk, hkn, h⟩
    rcases (show k = 1 ∨ k + 1 = n ∨ (2 ≤ k ∧ k + 2 ≤ n) by omega) with
      rfl | hk1 | ⟨hk2, hkn2⟩
    · rw [Nat.choose_one_right] at h
      exact Or.inl ⟨h, rfl⟩
    · rw [Nat.choose_symm_of_eq_add hk1.symm, Nat.choose_one_right] at h
      exact Or.inr (Or.inl ⟨h, by omega⟩)
    · right
      right
      by_cases hhalf : 2 * k ≤ n
      · exact Or.inl (mem_of_colsOK hcols htop hk2 hhalf h)
      · right
        have hsym : n.choose (n - k) = t := (Nat.choose_symm (by omega)).trans h
        exact ⟨(n, n - k), mem_of_colsOK hcols htop (by omega) (by omega) hsym, rfl,
          show n - (n - k) = k by omega⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hmem | ⟨⟨n', k'⟩, hmem, hn, hk⟩)
    · exact ⟨le_rfl, by omega, Nat.choose_one_right _⟩
    · exact ⟨by omega, by omega,
        (Nat.choose_symm_of_eq_add (by omega)).trans (Nat.choose_one_right _)⟩
    · obtain ⟨h1, h2, h3⟩ := validHalf_sound hS hmem
      dsimp only at h1 h2 h3
      exact ⟨by omega, by omega, h3⟩
    · obtain ⟨h1, h2, h3⟩ := validHalf_sound hS hmem
      dsimp only at h1 h2 h3 hn hk
      subst hn hk
      exact ⟨by omega, by omega, (Nat.choose_symm (by omega)).trans h3⟩

/-- All checks: `S` is valid, the column certificates hold, the columns from
`K = as.length + 2` on start above `t` (`K! t < (2K)(2K - 1) ⋯ (K + 1)`), and the positions
are distinct. -/
def certOK (t : ℕ) (S : List (ℕ × ℕ)) (as : List ℕ) : Bool :=
  validHalf t S && colsOK t S 2 as &&
    decide ((as.length + 2).factorial * t <
      (2 * (as.length + 2)).descFactorial (as.length + 2)) &&
    decide (positions t S).Nodup

/-- **Exact multiplicity from a certificate.** -/
theorem ncard_eq_of_certOK {t : ℕ} {S : List (ℕ × ℕ)} {as : List ℕ} (ht : 2 ≤ t)
    (h : certOK t S as = true) : (solutions t).ncard = 2 * S.length + 2 := by
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hS, hcols⟩, htop⟩, hnd⟩ := h
  rw [Nat.descFactorial_eq_factorial_mul_choose] at htop
  rw [solutions_eq_of_check ht hS hcols (Nat.lt_of_mul_lt_mul_left htop)]
  have e : {p | p ∈ positions t S} = ((positions t S).toFinset : Set (ℕ × ℕ)) := by
    ext p
    simp
  rw [e, Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd]
  simp only [positions, List.length_cons, List.length_append, List.length_map]
  omega

end Singmaster
