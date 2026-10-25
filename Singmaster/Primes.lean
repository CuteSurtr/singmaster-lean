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
import Singmaster.Window

/-!
# Numbers that appear exactly twice or exactly four times

A prime `p ≥ 3` appears only at `(p, 1)` and `(p, p - 1)`. A position `(n, k)` with
`2 ≤ k ≤ n - 2` would have `n < C(n, k) = p`, and no prime above `n` divides `C(n, k)`.

For a prime `p ≥ 5`, `C(p, 2)` appears only at `(p, 2)`, `(p, p - 2)` and the two edge positions.
A position `(n, k)` with `3 ≤ k` and `2k ≤ n` would lie in a row `n < p`, since otherwise
`C(n, k) ≥ C(n, 3) > C(n, 2) ≥ C(p, 2)`; but `p` divides `C(p, 2)` and no prime above `n` divides
`C(n, k)`.

So infinitely many numbers appear exactly twice and infinitely many appear exactly four times.
In the terms of Tovey (1985), infinitely many integers have exactly `0` and exactly `1`
representations `C(n, k)` with `1 < k ≤ n / 2`.

*Reference:* C. A. Tovey, *Multiple occurrences of binomial coefficients*, Fibonacci Quart. 23
(1985), 356-358.
-/

namespace Singmaster

/-- A prime `p ≥ 3` appears only at `(p, 1)` and `(p, p - 1)`. -/
theorem solutions_prime {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) :
    solutions p = {(p, 1), (p, p - 1)} := by
  ext ⟨n, k⟩
  simp only [mem_solutions, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hk, hkn, h⟩
    rcases (show k = 1 ∨ k + 1 = n ∨ (2 ≤ k ∧ k + 2 ≤ n) by omega) with
      rfl | hk1 | ⟨hk2, hkn2⟩
    · rw [Nat.choose_one_right] at h
      exact Or.inl ⟨h, rfl⟩
    · rw [Nat.choose_symm_of_eq_add hk1.symm, Nat.choose_one_right] at h
      exact Or.inr ⟨h, by omega⟩
    · exfalso
      have hlt : n < n.choose k := lt_choose hk2 hkn2
      rw [h] at hlt
      have hd : p ∣ n.choose k := ⟨1, by rw [h, mul_one]⟩
      exact not_prime_dvd_choose_of_lt hp (by omega) hlt hd
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨le_rfl, by omega, Nat.choose_one_right _⟩
    · exact ⟨by omega, by omega,
        (Nat.choose_symm_of_eq_add (by omega)).trans (Nat.choose_one_right _)⟩

/-- A prime `p ≥ 3` appears exactly twice. -/
theorem ncard_prime {p : ℕ} (hp : p.Prime) (h3 : 3 ≤ p) : (solutions p).ncard = 2 := by
  have hne : (p, 1) ≠ (p, p - 1) := by
    intro h
    rw [Prod.mk.injEq] at h
    omega
  rw [solutions_prime hp h3, Set.ncard_pair hne]

/-- `C(n, 2) < C(p, 2)` for `1 ≤ n < p`. -/
theorem choose_two_lt_of_lt {n p : ℕ} (hn : 1 ≤ n) (h : n < p) : n.choose 2 < p.choose 2 := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have h1 : n.choose 2 ≤ q.choose 2 := Nat.choose_le_choose 2 (by omega)
  have h2 : (q + 1).choose 2 = q.choose 1 + q.choose 2 := Nat.choose_succ_succ q 1
  rw [Nat.choose_one_right] at h2
  omega

/-- `C(n, 2) < C(n, 3)` for `n ≥ 6`. -/
theorem choose_two_lt_choose_three {n : ℕ} (hn : 6 ≤ n) : n.choose 2 < n.choose 3 := by
  have h : n.choose 3 * 3 = n.choose 2 * (n - 2) := Nat.choose_succ_right_eq n 2
  have hpos : 0 < n.choose 2 := Nat.choose_pos (by omega)
  have h4 : n.choose 2 * 4 ≤ n.choose 2 * (n - 2) := Nat.mul_le_mul (le_refl _) (by omega)
  omega

/-- For a prime `p ≥ 5`, the only position `(n, k)` of `C(p, 2)` with `2 ≤ k` and `2k ≤ n` is
`(p, 2)`. -/
theorem eq_of_choose_eq_choose_prime_two {p n k : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) (hk : 2 ≤ k)
    (hkn : 2 * k ≤ n) (h : n.choose k = p.choose 2) : n = p ∧ k = 2 := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk3
  · refine ⟨?_, rfl⟩
    rcases lt_trichotomy n p with hnp | rfl | hnp
    · have := choose_two_lt_of_lt (by omega) hnp
      omega
    · rfl
    · have := choose_two_lt_of_lt (by omega) hnp
      omega
  · exfalso
    have hn : n < p := by
      by_contra hc
      have h1 : n.choose 3 ≤ n.choose k := choose_le_choose_of_le_of_two_mul_le (by omega) hkn
      have h2 : n.choose 2 < n.choose 3 := choose_two_lt_choose_three (by omega)
      have h3 : p.choose 2 ≤ n.choose 2 := Nat.choose_le_choose 2 (by omega)
      omega
    have hd : p ∣ n.choose k := by
      rw [h]
      exact hp.dvd_choose_self (by norm_num) (by omega)
    exact not_prime_dvd_choose_of_lt hp (by omega) hn hd

/-- For a prime `p ≥ 5`, `C(p, 2)` appears only at `(C(p, 2), 1)`, `(C(p, 2), C(p, 2) - 1)`,
`(p, 2)` and `(p, p - 2)`. -/
theorem solutions_choose_prime_two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    solutions (p.choose 2) =
      {(p.choose 2, 1), (p.choose 2, p.choose 2 - 1), (p, 2), (p, p - 2)} := by
  have hpt : p < p.choose 2 := lt_choose (le_refl 2) (by omega)
  ext ⟨n, k⟩
  simp only [mem_solutions, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
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
      · exact Or.inl (eq_of_choose_eq_choose_prime_two hp h5 hk2 hhalf h)
      · have hsym : n.choose (n - k) = p.choose 2 := (Nat.choose_symm (by omega)).trans h
        obtain ⟨rfl, h2⟩ := eq_of_choose_eq_choose_prime_two hp h5 (by omega) (by omega) hsym
        exact Or.inr ⟨rfl, by omega⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨le_rfl, by omega, Nat.choose_one_right _⟩
    · exact ⟨by omega, by omega,
        (Nat.choose_symm_of_eq_add (by omega)).trans (Nat.choose_one_right _)⟩
    · exact ⟨by norm_num, by omega, rfl⟩
    · exact ⟨by omega, by omega, Nat.choose_symm (by omega)⟩

/-- For a prime `p ≥ 5`, `C(p, 2)` appears exactly four times. -/
theorem ncard_choose_prime_two {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) :
    (solutions (p.choose 2)).ncard = 4 := by
  have hpt : p < p.choose 2 := lt_choose (le_refl 2) (by omega)
  have h1 : (p.choose 2, 1) ∉
      ({(p.choose 2, p.choose 2 - 1), (p, 2), (p, p - 2)} : Set (ℕ × ℕ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have h2 : (p.choose 2, p.choose 2 - 1) ∉ ({(p, 2), (p, p - 2)} : Set (ℕ × ℕ)) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
    omega
  have h3 : (p, 2) ≠ (p, p - 2) := by
    intro h
    rw [Prod.mk.injEq] at h
    omega
  rw [solutions_choose_prime_two hp h5, Set.ncard_insert_of_notMem h1,
    Set.ncard_insert_of_notMem h2, Set.ncard_pair h3]

/-- **Infinitely many numbers appear exactly twice** in Pascal's triangle. -/
theorem singmaster.variants.infinite_ncard_eq_two : {t : ℕ | (solutions t).ncard = 2}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 3)
  have := hM (show p ∈ {t : ℕ | (solutions t).ncard = 2} from ncard_prime hp (by omega))
  omega

/-- **Infinitely many numbers appear exactly four times** in Pascal's triangle. -/
theorem singmaster.variants.infinite_ncard_eq_four :
    {t : ℕ | (solutions t).ncard = 4}.Infinite := by
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  obtain ⟨p, hpM, hp⟩ := Nat.exists_infinite_primes (M + 5)
  have h4 := ncard_choose_prime_two hp (by omega)
  have := hM (show p.choose 2 ∈ {t : ℕ | (solutions t).ncard = 4} from h4)
  have hpt : p < p.choose 2 := lt_choose (le_refl 2) (by omega)
  omega

end Singmaster
