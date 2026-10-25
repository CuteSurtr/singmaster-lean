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
import Singmaster.Fibonacci

/-!
# Collisions between adjacent rows

**Lind's theorem** (1968): for `1 ≤ k` and `k + 2 ≤ n`, `C(n, k) = C(n - 1, k + 1)` holds exactly
when `n = F(2i+2) F(2i+3)` and `k = F(2i) F(2i+3)` for some `i ≥ 1`. So the family of
`Singmaster.choose_fib_eq` contains every collision between adjacent rows.

The proof: write `s = k + 1` and `r = n - k - 1`. Then `C(n, k) = C(n - 1, k + 1)` says
`(s + r) s = (r + 1) r`, and with `c = r + 1 - s` this becomes `s² + c = s c + c²`. A gcd argument
shows `c = b²` and `s = b (a + b)` with `b² = a b + a² + 1`. The solutions of that equation are
`a = F(2i)`, `b = F(2i+1)`, by descent `(a, b) ↦ (2a - b, b - a)`.

*References:*
- D. A. Lind, *The quadratic field Q(√5) and a certain Diophantine equation*,
  Fibonacci Quart. 6 (1968), 86-93.
- D. Singmaster, *Repeated binomial coefficients and Fibonacci numbers*,
  Fibonacci Quart. 13 (1975), 295-298.
- C. A. Tovey, *Multiple occurrences of binomial coefficients*, Fibonacci Quart. 23 (1985),
  356-358 (Theorem 2).
-/

open Nat

namespace Singmaster

/-- `C(k + d + 1, k) = C(k + d, k + 1)` iff `(k + d + 1)(k + 1) = (d + 1) d`. -/
theorem choose_eq_choose_pred_succ_iff {k d : ℕ} :
    (k + d + 1).choose k = (k + d).choose (k + 1) ↔ (k + d + 1) * (k + 1) = (d + 1) * d := by
  refine ⟨fun h => ?_, choose_eq_choose_pred_succ⟩
  have ha : (k + d).choose (k + 1) * (k + 1) = (k + d).choose k * d := by
    have := Nat.choose_succ_right_eq (k + d) k
    rwa [Nat.add_sub_cancel_left] at this
  have hb : (k + d + 1) * (k + d).choose k = (k + d + 1).choose (k + 1) * (k + 1) :=
    Nat.add_one_mul_choose_eq (k + d) k
  have hc : (k + d + 1).choose (k + 1) * (k + 1) = (k + d + 1).choose k * (d + 1) := by
    have := Nat.choose_succ_right_eq (k + d + 1) k
    rwa [show k + d + 1 - k = d + 1 by omega] at this
  have e1 : (k + d + 1).choose k * (d + 1) = (k + d + 1) * (k + d).choose k :=
    hc.symm.trans hb.symm
  have e2 : (k + d + 1).choose k * (k + 1) = (k + d).choose k * d := by
    rw [h]
    exact ha
  have hX : 0 < (k + d + 1).choose k := Nat.choose_pos (by omega)
  have hY : 0 < (k + d).choose k := Nat.choose_pos (by omega)
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hX hY)
  calc (k + d + 1).choose k * (k + d).choose k * ((k + d + 1) * (k + 1))
      = ((k + d + 1) * (k + d).choose k) * ((k + d + 1).choose k * (k + 1)) := by ring
    _ = ((k + d + 1).choose k * (d + 1)) * ((k + d).choose k * d) := by rw [e1, e2]
    _ = (k + d + 1).choose k * (k + d).choose k * ((d + 1) * d) := by ring

/-- The solutions of `b² = a b + a² + 1` are `a = F(2i)`, `b = F(2i+1)`. -/
theorem exists_fib_of_cassini (a : ℕ) :
    ∀ b, b ^ 2 = a * b + a ^ 2 + 1 → ∃ i, a = fib (2 * i) ∧ b = fib (2 * i + 1) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro b h
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · have h1 : b * b = 1 := by nlinarith [h]
      have hb : b = 1 := Nat.eq_one_of_mul_eq_one_right h1
      exact ⟨0, by simp, by simp [hb]⟩
    · have hab : a < b := by
        by_contra hc
        have hc' : b ≤ a := Nat.le_of_not_lt hc
        have := Nat.mul_le_mul hc' (le_refl b)
        nlinarith [h]
      have hb2 : b ≤ 2 * a := by
        by_contra hc
        have hc' : 2 * a + 1 ≤ b := by omega
        have h1 := Nat.mul_le_mul hc' (le_refl b)
        have h2 := Nat.mul_le_mul (le_refl a) hc'
        nlinarith [h]
      obtain ⟨b', rfl⟩ : ∃ b', b = a + b' := ⟨b - a, by omega⟩
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + b' := ⟨a - b', by omega⟩
      have h' : b' ^ 2 = a' * b' + a' ^ 2 + 1 := by nlinarith [h]
      obtain ⟨i, hi1, hi2⟩ := ih a' (by omega) b' h'
      refine ⟨i + 1, ?_, ?_⟩
      · rw [show 2 * (i + 1) = 2 * i + 2 by ring, fib_two_mul_add_two, ← hi1, ← hi2]
      · rw [show 2 * (i + 1) + 1 = 2 * i + 3 by ring, fib_two_mul_add_three, ← hi1, ← hi2]
        ring

/-- If `s² + c = s c + c²` with `1 ≤ s`, then `c = b²` and `s = b (a + b)` for some `a, b` with
`b² = a b + a² + 1`. -/
theorem exists_cassini_of_eq {s c : ℕ} (hs : 1 ≤ s) (key : s * s + c = s * c + c * c) :
    ∃ a b, b ^ 2 = a * b + a ^ 2 + 1 ∧ s = b * (a + b) ∧ c = b * b := by
  have hg : 0 < Nat.gcd s c := Nat.gcd_pos_of_pos_left c (by omega)
  obtain ⟨g, s1, c1, hg0, hcop, rfl, rfl⟩ := Nat.exists_coprime' hg
  have key2 : s1 * s1 * g + c1 = s1 * c1 * g + c1 * c1 * g := by
    apply Nat.eq_of_mul_eq_mul_left hg0
    nlinarith [key]
  have hgd : g ∣ c1 := by
    have h1 : g ∣ c1 + s1 * s1 * g := by
      rw [show c1 + s1 * s1 * g = (s1 * c1 + c1 * c1) * g by nlinarith [key2]]
      exact dvd_mul_left g _
    exact (Nat.dvd_add_left (dvd_mul_left g (s1 * s1))).mp h1
  have hcd : c1 ∣ g := by
    have h1 : c1 ∣ s1 * s1 * g + c1 := by
      rw [key2]
      exact ⟨s1 * g + c1 * g, by ring⟩
    have h2 : c1 ∣ s1 * s1 * g := (Nat.dvd_add_left (dvd_refl c1)).mp h1
    exact (Nat.Coprime.mul_right hcop.symm hcop.symm).dvd_of_dvd_mul_left h2
  have hgc : c1 = g := Nat.dvd_antisymm hcd hgd
  subst c1
  have key3 : s1 * s1 + 1 = s1 * g + g * g := by
    apply Nat.eq_of_mul_eq_mul_left hg0
    nlinarith [key2]
  have hgs : g ≤ s1 := by
    by_contra hc
    have hc' : s1 + 1 ≤ g := by omega
    rcases Nat.eq_zero_or_pos s1 with h0 | h0
    · subst h0
      omega
    · have h1 := Nat.mul_le_mul hc' hc'
      have h2 := Nat.mul_le_mul (le_refl s1) hc'
      nlinarith [key3]
  obtain ⟨a, rfl⟩ : ∃ a, s1 = a + g := ⟨s1 - g, by omega⟩
  exact ⟨a, g, by nlinarith [key3], by ring, rfl⟩

/-- If `(s + r) s = (r + 1) r` with `1 ≤ s`, then `s = b (a + b)` and `r + 1 = b (a + 2b)` for
some `a, b` with `b² = a b + a² + 1`. -/
theorem exists_cassini_of_adjacent {s r : ℕ} (hs : 1 ≤ s) (h : (s + r) * s = (r + 1) * r) :
    ∃ a b, b ^ 2 = a * b + a ^ 2 + 1 ∧ s = b * (a + b) ∧ r + 1 = b * (a + 2 * b) := by
  have hsr : s ≤ r := by
    by_contra hc
    have hc' : r + 1 ≤ s := by omega
    have h1 := Nat.mul_le_mul hc' hc'
    have h2 := Nat.mul_le_mul (le_refl r) hc'
    nlinarith [h]
  obtain ⟨c, rfl⟩ : ∃ c, r = s + c := ⟨r - s, by omega⟩
  have key : s * s + (c + 1) = s * (c + 1) + (c + 1) * (c + 1) := by nlinarith [h]
  obtain ⟨a, b, hab, hs', hc'⟩ := exists_cassini_of_eq hs key
  refine ⟨a, b, hab, hs', ?_⟩
  rw [show s + c + 1 = s + (c + 1) by ring, hs', hc']
  ring

/-- **Lind's theorem.** For `1 ≤ k` and `k + 2 ≤ n`, `C(n, k) = C(n - 1, k + 1)` iff
`n = F(2i+2) F(2i+3)` and `k = F(2i) F(2i+3)` for some `i ≥ 1`. -/
theorem choose_eq_choose_pred_succ_iff_fib {n k : ℕ} (hk : 1 ≤ k) (hkn : k + 2 ≤ n) :
    n.choose k = (n - 1).choose (k + 1) ↔
      ∃ i, 1 ≤ i ∧ n = fib (2 * i + 2) * fib (2 * i + 3) ∧ k = fib (2 * i) * fib (2 * i + 3) := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d + 1 := ⟨n - k - 1, by omega⟩
  rw [show k + d + 1 - 1 = k + d by omega]
  constructor
  · intro h
    have h1 := choose_eq_choose_pred_succ_iff.1 h
    have h2 : (k + 1 + d) * (k + 1) = (d + 1) * d := by
      rw [← h1]
      ring
    obtain ⟨a, b, hab, hs, hr⟩ := exists_cassini_of_adjacent (by omega) h2
    obtain ⟨i, rfl, rfl⟩ := exists_fib_of_cassini a b hab
    refine ⟨i, ?_, ?_, ?_⟩
    · by_contra hi
      obtain rfl : i = 0 := by omega
      norm_num at hs
      omega
    · rw [fib_two_mul_add_two, fib_two_mul_add_three]
      nlinarith [hab, hs, hr]
    · rw [fib_two_mul_add_three]
      nlinarith [hab, hs]
  · rintro ⟨i, -, hn, hk'⟩
    have := choose_fib_eq i
    rw [← hn, ← hk', show k + d + 1 - 1 = k + d by omega] at this
    exact this

end Singmaster
