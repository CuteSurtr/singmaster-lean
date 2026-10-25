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
# The rules behind the computer searches

The searches for further representations `t = C(n, k)` (in `research/search/singsearch.py` on
the `search` branch) rest on three facts, proved here.

* **Bracket.** `(n + 1 - k) ^ k ≤ k! C(n, k) ≤ n ^ k`, so for fixed `k` and `t` a solution `n`
  lies in a window of `k` consecutive integers determined by `(k! t)^(1/k)`.
* **Window lemma.** For a prime `p > k`, `p` divides `C(n, k)` exactly when `p` divides one of the
  `k` numbers `n, n - 1, …, n - k + 1`, because `k! C(n, k) = n (n - 1) ⋯ (n - k + 1)` and `p` does
  not divide `k!`.
* **Central case.** If `C(n, k) = C(2m, m)` with `k < m`, then `n > 2m`, every prime in `(m, 2m]`
  divides one of `n, …, n - k + 1`, and no prime above `2m` divides any of them.
-/

namespace Singmaster

/-- **Bracket.** `(n + 1 - k) ^ k ≤ k! C(n, k) ≤ n ^ k`. -/
theorem pow_le_factorial_mul_choose_le (n k : ℕ) :
    (n + 1 - k) ^ k ≤ k.factorial * n.choose k ∧ k.factorial * n.choose k ≤ n ^ k := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact ⟨Nat.pow_sub_le_descFactorial n k, Nat.descFactorial_le_pow n k⟩

/-- A prime divides `n (n - 1) ⋯ (n - k + 1)` iff it divides one of the `k` factors. -/
theorem prime_dvd_descFactorial_iff {p n : ℕ} (hp : p.Prime) (k : ℕ) :
    p ∣ n.descFactorial k ↔ ∃ j < k, p ∣ n - j := by
  induction k with
  | zero =>
    constructor
    · intro h
      rw [Nat.descFactorial_zero, Nat.dvd_one] at h
      exact absurd h hp.one_lt.ne'
    · rintro ⟨j, hj, -⟩
      omega
  | succ k ih =>
    rw [Nat.descFactorial_succ, hp.dvd_mul, ih]
    constructor
    · rintro (h | ⟨j, hj, h⟩)
      · exact ⟨k, by omega, h⟩
      · exact ⟨j, by omega, h⟩
    · rintro ⟨j, hj, h⟩
      by_cases hjk : j = k
      · subst hjk
        exact Or.inl h
      · exact Or.inr ⟨j, by omega, h⟩

/-- **Window lemma.** For a prime `p > k`, `p ∣ C(n, k)` iff `p ∣ n - j` for some `j < k`. -/
theorem prime_dvd_choose_iff_window {p n k : ℕ} (hp : p.Prime) (hkp : k < p) :
    p ∣ n.choose k ↔ ∃ j < k, p ∣ n - j := by
  have hfac : ¬ p ∣ k.factorial := by
    rw [hp.dvd_factorial]
    omega
  have h1 : p ∣ n.descFactorial k ↔ p ∣ n.choose k := by
    rw [Nat.descFactorial_eq_factorial_mul_choose, hp.dvd_mul]
    exact ⟨fun h => h.resolve_left hfac, Or.inr⟩
  exact h1.symm.trans (prime_dvd_descFactorial_iff hp k)

/-- No prime above `N` divides `C(N, K)` for `K ≤ N`. -/
theorem not_prime_dvd_choose_of_lt {N K p : ℕ} (hp : p.Prime) (hK : K ≤ N) (hN : N < p) :
    ¬ p ∣ N.choose K := by
  intro hd
  have h1 : N.choose K ∣ N.factorial :=
    ⟨K.factorial * (N - K).factorial, by
      rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial hK]⟩
  have := hp.dvd_factorial.1 (hd.trans h1)
  omega

/-- For `k < m`, `C(2m, k) < C(2m, m)`. -/
theorem choose_lt_centralBinom {m k : ℕ} (hkm : k < m) : (2 * m).choose k < Nat.centralBinom m := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  have h1 := Nat.choose_succ_right_eq (2 * m) k
  have h2 : 0 < (2 * m).choose k := Nat.choose_pos (by omega)
  have h3 : (2 * m).choose (k + 1) ≤ (2 * m).choose m :=
    choose_le_choose_of_le_of_two_mul_le (by omega) (by omega)
  have h4 : k + 1 < 2 * m - k := by omega
  have h5 : (2 * m).choose k * (k + 1) < (2 * m).choose (k + 1) * (k + 1) := by
    rw [h1]
    nlinarith [h2, h4]
  exact (Nat.lt_of_mul_lt_mul_right h5).trans_le h3

/-- A second representation `C(n, k) = C(2m, m)` with `k < m` lies in a row `n > 2m`. -/
theorem two_mul_lt_of_choose_eq_centralBinom {m n k : ℕ} (hkm : k < m)
    (h : n.choose k = Nat.centralBinom m) : 2 * m < n := by
  by_contra hn
  have h1 : n.choose k ≤ (2 * m).choose k := Nat.choose_le_choose k (by omega)
  have h2 := choose_lt_centralBinom hkm
  omega

/-- Every prime in `(m, 2m]` divides `C(2m, m)`. -/
theorem prime_dvd_centralBinom {m p : ℕ} (hp : p.Prime) (h1 : m < p) (h2 : p ≤ 2 * m) :
    p ∣ Nat.centralBinom m := by
  rw [Nat.centralBinom_eq_two_mul_choose]
  exact hp.dvd_choose h1 (by omega) h2

/-- **Pruning rules of the central search.** If `C(n, k) = C(2m, m)` with `k < m`, then `n > 2m`,
every prime in `(m, 2m]` divides one of `n, n - 1, …, n - k + 1`, and no prime above `2m`
divides any of them. -/
theorem central_window {m n k : ℕ} (hkm : k < m) (h : n.choose k = Nat.centralBinom m) :
    2 * m < n ∧ (∀ p, p.Prime → m < p → p ≤ 2 * m → ∃ j < k, p ∣ n - j) ∧
      ∀ p, p.Prime → 2 * m < p → ∀ j < k, ¬ p ∣ n - j := by
  refine ⟨two_mul_lt_of_choose_eq_centralBinom hkm h, ?_, ?_⟩
  · intro p hp h1 h2
    have hd : p ∣ n.choose k := by
      rw [h]
      exact prime_dvd_centralBinom hp h1 h2
    exact (prime_dvd_choose_iff_window hp (by omega)).1 hd
  · intro p hp h1 j hj hd
    have hc : p ∣ n.choose k := (prime_dvd_choose_iff_window hp (by omega)).2 ⟨j, hj, hd⟩
    rw [h, Nat.centralBinom_eq_two_mul_choose] at hc
    exact not_prime_dvd_choose_of_lt hp (by omega) h1 hc

/-- **Pruning rules for any value `t = C(N, K)`.** A representation `C(n, k) = C(N, K)` with
`K ≤ N` has no prime `p > max(k, N)` dividing any of `n, n - 1, …, n - k + 1`, and for every prime
`p > k` the window contains a multiple of `p` exactly when `p` divides `C(N, K)`. -/
theorem choose_eq_window {N K n k : ℕ} (hK : K ≤ N) (h : n.choose k = N.choose K) :
    (∀ p, p.Prime → k < p → (p ∣ N.choose K ↔ ∃ j < k, p ∣ n - j)) ∧
      ∀ p, p.Prime → k < p → N < p → ∀ j < k, ¬ p ∣ n - j := by
  refine ⟨fun p hp hkp => by rw [← h]; exact prime_dvd_choose_iff_window hp hkp, ?_⟩
  intro p hp hkp hN j hj hd
  have hc : p ∣ n.choose k := (prime_dvd_choose_iff_window hp hkp).2 ⟨j, hj, hd⟩
  rw [h] at hc
  exact not_prime_dvd_choose_of_lt hp hK hN hc

end Singmaster
