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
import Mathlib

/-!
# Singmaster's conjecture: definitions and row bounds

`Singmaster.solutions t` is the set of positions `(n, k)` with `1 ≤ k < n` at which `t` appears
in Pascal's triangle. The definition is copied from `FormalConjectures/Wikipedia/Singmaster.lean`
in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
so `(solutions t).ncard` is the quantity that the open conjecture there bounds.

This file proves the facts about rows of Pascal's triangle that the solved cases use:
rows are unimodal, every entry off the edges of row `n` is at least `n`, and `solutions t` is
finite.

*Reference:* [Wikipedia](https://en.wikipedia.org/wiki/Singmaster%27s_conjecture)
-/

namespace Singmaster

/--
The set of pairs `(n, k)` representing the solutions to the equation
`Nat.choose n k = t` for a given `t`, under the constraint `1 ≤ k < n`.
-/
def solutions (t : ℕ) : Set (ℕ × ℕ) :=
  {(n, k) | 1 ≤ k ∧ k < n ∧ Nat.choose n k = t}

@[simp]
theorem mem_solutions {t n k : ℕ} : (n, k) ∈ solutions t ↔ 1 ≤ k ∧ k < n ∧ n.choose k = t :=
  Iff.rfl

/-- Row `n` of Pascal's triangle is increasing on its left half. -/
theorem choose_le_choose_of_le_of_two_mul_le {n j k : ℕ} (hjk : j ≤ k) (hk : 2 * k ≤ n) :
    n.choose j ≤ n.choose k := by
  revert hk
  induction k, hjk using Nat.le_induction with
  | base => exact fun _ ↦ le_rfl
  | succ k _ ih =>
    intro hk
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Row `n` of Pascal's triangle is unimodal: an entry at distance at least `j` from both edges is
at least `C(n, j)`. -/
theorem choose_le_choose_of_le_of_le_sub {n j k : ℕ} (hjk : j ≤ k) (hkn : k ≤ n - j) :
    n.choose j ≤ n.choose k := by
  rcases le_total (2 * k) n with h | h
  · exact choose_le_choose_of_le_of_two_mul_le hjk h
  · rw [← Nat.choose_symm (show k ≤ n by omega)]
    exact choose_le_choose_of_le_of_two_mul_le (by omega) (by omega)

/-- Off the edges, every entry of row `n` is at least `n`. -/
theorem le_choose {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) : n ≤ n.choose k := by
  have h := choose_le_choose_of_le_of_le_sub hk (show k ≤ n - 1 by omega)
  rwa [Nat.choose_one_right] at h

/-- Two steps in from both edges, every entry of row `n` exceeds `n`. -/
theorem lt_choose {n k : ℕ} (hk : 2 ≤ k) (hkn : k + 2 ≤ n) : n < n.choose k := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : (m + 1).choose 2 ≤ (m + 1).choose k := choose_le_choose_of_le_of_le_sub hk (by omega)
  have h2 : (m + 1).choose 2 = m.choose 1 + m.choose 2 := Nat.choose_succ_succ m 1
  have h3 : m.choose 1 ≤ m.choose 2 := choose_le_choose_of_le_of_le_sub (by norm_num) (by omega)
  rw [Nat.choose_one_right] at h2 h3
  omega

/-- Every position of `t` lies in the square `[0, t] × [0, t]`. -/
theorem solutions_subset (t : ℕ) : solutions t ⊆ Set.Iic t ×ˢ Set.Iic t := by
  rintro ⟨n, k⟩ hp
  obtain ⟨hk, hkn, h⟩ := mem_solutions.1 hp
  have := le_choose hk hkn
  simp only [Set.mem_prod, Set.mem_Iic]
  omega

/-- Every number appears only finitely often in Pascal's triangle. -/
theorem solutions_finite (t : ℕ) : (solutions t).Finite :=
  ((Set.finite_Iic t).prod (Set.finite_Iic t)).subset (solutions_subset t)

end Singmaster
