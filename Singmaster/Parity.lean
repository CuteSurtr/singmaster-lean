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
# Odd multiplicities come from central binomial coefficients

The positions of `t` pair up as `(n, k)` and `(n, n - k)`. A position is its own partner only
when `n = 2k`. So if `t` appears an odd number of times, then `t = C(2m, m)` for some `m ≥ 1`.
In particular, a number that appears exactly 5 or 7 times is a central binomial coefficient
`C(2m, m)` that equals some `C(n, k)` with `2 ≤ k < n / 2`.
-/

namespace Singmaster

/-- The mirror image `(n, n - k)` of the position `(n, k)`. -/
def mirror (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.1 - p.2)

/-- Positions in the left half of their row. -/
def leftHalf (t : ℕ) : Set (ℕ × ℕ) := {p | p ∈ solutions t ∧ 2 * p.2 < p.1}

/-- Positions in the right half of their row. -/
def rightHalf (t : ℕ) : Set (ℕ × ℕ) := {p | p ∈ solutions t ∧ p.1 < 2 * p.2}

theorem mem_leftHalf {t : ℕ} {p : ℕ × ℕ} :
    p ∈ leftHalf t ↔ p ∈ solutions t ∧ 2 * p.2 < p.1 :=
  Iff.rfl

theorem mem_rightHalf {t : ℕ} {p : ℕ × ℕ} :
    p ∈ rightHalf t ↔ p ∈ solutions t ∧ p.1 < 2 * p.2 :=
  Iff.rfl

theorem mirror_mem {t n k : ℕ} (hp : (n, k) ∈ solutions t) : (n, n - k) ∈ solutions t := by
  obtain ⟨hk, hkn, h⟩ := mem_solutions.1 hp
  exact mem_solutions.2 ⟨by omega, by omega, (Nat.choose_symm hkn.le).trans h⟩

theorem rightHalf_eq_image (t : ℕ) : rightHalf t = mirror '' leftHalf t := by
  ext ⟨n, k⟩
  simp only [mem_rightHalf, mem_leftHalf, Set.mem_image, Prod.exists, mirror, Prod.mk.injEq]
  constructor
  · rintro ⟨hp, hlt⟩
    have hkn := (mem_solutions.1 hp).2.1
    exact ⟨n, n - k, ⟨mirror_mem hp, by omega⟩, rfl, by omega⟩
  · rintro ⟨n', k', ⟨hp', hlt'⟩, rfl, rfl⟩
    have hkn := (mem_solutions.1 hp').2.1
    exact ⟨mirror_mem hp', by omega⟩

theorem mirror_injOn (t : ℕ) : Set.InjOn mirror (leftHalf t) := by
  rintro ⟨n, k⟩ ⟨hp, -⟩ ⟨n', k'⟩ ⟨hp', -⟩ h
  have hk := (mem_solutions.1 hp).2.1
  have hk' := (mem_solutions.1 hp').2.1
  simp only [mirror, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  simp only [Prod.mk.injEq, true_and]
  omega

/-- If no position of `t` is the middle of an even row, then `t` appears an even number of
times. -/
theorem ncard_eq_two_mul_of_no_center {t : ℕ} (hc : ∀ m, (2 * m, m) ∉ solutions t) :
    (solutions t).ncard = 2 * (leftHalf t).ncard := by
  have hfin := solutions_finite t
  have hsplit : solutions t = leftHalf t ∪ rightHalf t := by
    ext ⟨n, k⟩
    simp only [mem_leftHalf, mem_rightHalf, Set.mem_union]
    constructor
    · intro hp
      rcases lt_trichotomy (2 * k) n with h1 | h1 | h1
      · exact Or.inl ⟨hp, h1⟩
      · exact absurd (by rw [h1]; exact hp) (hc k)
      · exact Or.inr ⟨hp, h1⟩
    · rintro (⟨hp, -⟩ | ⟨hp, -⟩) <;> exact hp
  have hdisj : Disjoint (leftHalf t) (rightHalf t) := by
    rw [Set.disjoint_left]
    rintro ⟨n, k⟩ ⟨-, h1⟩ ⟨-, h2⟩
    change 2 * k < n at h1
    change n < 2 * k at h2
    omega
  have hL : (leftHalf t).Finite := hfin.subset fun p hp => hp.1
  have hR : (rightHalf t).Finite := hfin.subset fun p hp => hp.1
  rw [hsplit, Set.ncard_union_eq hdisj hL hR, rightHalf_eq_image, (mirror_injOn t).ncard_image]
  ring

/-- **Odd multiplicities.** If `t` appears an odd number of times in Pascal's triangle, then
`t = C(2m, m)` for some `m ≥ 1`. -/
theorem exists_centralBinom_of_odd_ncard {t : ℕ} (h : Odd (solutions t).ncard) :
    ∃ m, 1 ≤ m ∧ t = Nat.centralBinom m := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have hnc : ∀ m, (2 * m, m) ∉ solutions t := by
    intro m hm
    obtain ⟨h1, -, h3⟩ := mem_solutions.1 hm
    exact hc m h1 (by rw [Nat.centralBinom_eq_two_mul_choose]; exact h3.symm)
  obtain ⟨r, hr⟩ := h
  have := ncard_eq_two_mul_of_no_center hnc
  omega

/-- A number that appears exactly 5 or exactly 7 times is a central binomial coefficient. -/
theorem exists_centralBinom_of_ncard_eq_five_or_seven {t : ℕ}
    (h : (solutions t).ncard = 5 ∨ (solutions t).ncard = 7) :
    ∃ m, 1 ≤ m ∧ t = Nat.centralBinom m :=
  exists_centralBinom_of_odd_ncard (by
    rcases h with h | h
    · rw [h]
      exact ⟨2, rfl⟩
    · rw [h]
      exact ⟨3, rfl⟩)

end Singmaster
