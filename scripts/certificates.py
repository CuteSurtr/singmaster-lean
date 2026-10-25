#!/usr/bin/env python3
"""Regenerate Singmaster/Collisions.lean and Singmaster/Central.lean.

    python3 scripts/certificates.py [M]        (default M = 200)

For a number t and its positions S with 2 <= k and 2k <= n, the certificate for column k is the
largest row a with C(a, k) < t, for k = 2, ..., K - 1, where K is the least k with C(2k, k) > t.
Singmaster/Certified.lean checks every certificate in the kernel, so this script is not trusted:
a wrong certificate makes the build fail, it cannot make Lean accept a false statement.
Central.lean covers C(2m, m) for 2 <= m <= M.
"""
import os
import sys
from math import comb

import sys
from math import comb


def kmax_of(t):
    k = 1
    while comb(2 * (k + 1), k + 1) <= t:
        k += 1
    return k


def largest_below(t, k):
    """Largest n >= k - 1 with C(n, k) < t."""
    lo = k - 1          # C(k-1, k) = 0 < t
    hi = k
    while comb(hi, k) < t:
        hi *= 2
    # C(lo, k) < t <= C(hi, k)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if comb(mid, k) < t:
            lo = mid
        else:
            hi = mid
    return lo


def cert(t, S):
    S = set(S)
    km = kmax_of(t)
    as_ = []
    found = []
    for k in range(2, km + 1):
        a = largest_below(t, k)
        assert comb(a, k) < t
        if (a + 1, k) in S:
            assert comb(a + 1, k) == t and t < comb(a + 2, k)
        else:
            if comb(a + 1, k) == t:
                found.append((a + 1, k))
            assert t < comb(a + 1, k), ("unexpected solution", a + 1, k)
        as_.append(a)
    assert len(as_) + 2 == km + 1
    assert t < comb(2 * (km + 1), km + 1)
    return km, as_, found


def lean_list(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"



ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
HEADER = open(os.path.join(ROOT, "Singmaster", "Basic.lean")).read().split("-/", 1)[0] + "-/\n"
OUT = os.path.join(ROOT, "Singmaster")
M = int(sys.argv[1]) if len(sys.argv) > 1 else 200


def wrap(xs, indent="    ", width=100):
    """Lean list literal wrapped to `width` columns."""
    lines, cur = [], indent + "["
    for i, x in enumerate(xs):
        s = str(x) + ("," if i < len(xs) - 1 else "]")
        if len(cur) + len(s) + 1 > width:
            lines.append(cur.rstrip())
            cur = indent + " " + s
        else:
            cur += ("" if cur.endswith("[") else " ") + s
    lines.append(cur)
    return "\n".join(lines)


def wrap_num(n, indent="    ", width=100):
    s = str(n)
    if len(indent) + len(s) <= width:
        return indent + s
    # Lean has no digit separators in literals, so long numbers stay on one line.
    return indent + s


small = [
    (120, [(16, 2), (10, 3)]),
    (210, [(21, 2), (10, 4)]),
    (1540, [(56, 2), (22, 3)]),
    (7140, [(120, 2), (36, 3)]),
    (11628, [(153, 2), (19, 5)]),
    (24310, [(221, 2), (17, 8)]),
]

col = []
col.append(HEADER)
col.append("""import Singmaster.Certified
import Singmaster.Fibonacci

/-!
# Exact multiplicities of the known repeated numbers

Besides `3003`, which appears eight times (`Singmaster.N3003`), every number known to appear
more than four times in Pascal's triangle is one of `120, 210, 1540, 7140, 11628, 24310`, or a
Lind–Singmaster number `C(F(2i+2) F(2i+3), F(2i) F(2i+3))` with `i ≥ 2`. The certificates of
`Singmaster.Certified` show that each of the six small numbers appears exactly six times, and
so do the Lind–Singmaster numbers for `i = 2` (`C(104, 39)`, 29 digits), `i = 3`
(`C(714, 272)`, 205 digits) and `i = 4` (`C(4895, 1869)`, 1412 digits).

Each certificate lists, for every column `k = 2, …, K - 1`, the largest row `a` with
`C(a, k) < t`. The kernel checks them with `decide +kernel`. They were produced by
`scripts/certificates.py`, which is not trusted: a wrong certificate fails the check.
-/

open Nat

namespace Singmaster
""")

for t, S in small:
    km, as_, found = cert(t, S)
    assert not found
    Ss = "[" + ", ".join(f"({n}, {k})" for n, k in S) + "]"
    reps = " = ".join(f"C({n}, {k})" for n, k in S)
    col.append(f"""/-- `{t} = {reps}` appears exactly six times in Pascal's triangle. -/
theorem ncard_{t} : (solutions {t}).ncard = 6 :=
  (ncard_eq_of_certOK (S := {Ss}) (as := {lean_list(as_)})
    (by norm_num) (by decide +kernel)).trans (by decide)
""")

# (i, N, K, maxHeartbeats for the count or None for the default). For i = 4 the check uses
# 425,055 heartbeats (measured with `#count_heartbeats in` on Lean v4.35.0).
lind = [(2, 104, 39, None), (3, 714, 272, None), (4, 4895, 1869, 1000000)]
for i, N, K, heartbeats in lind:
    t = comb(N, K)
    km, as_, found = cert(t, [(N, K), (N - 1, K + 1)])
    assert not found
    digits = len(str(t))
    rec_opt = ("-- The default `maxRecDepth` is too small to elaborate this list.\n"
               "set_option maxRecDepth 100000 in\n") if len(as_) > 1000 else ""
    hb_opt = (f"-- The kernel check needs more than the default 200000 heartbeats.\n"
              f"set_option maxHeartbeats {heartbeats} in\n") if heartbeats else ""
    col.append(f"""theorem choose_{N}_{K} : ({N} : ℕ).choose {K} =
{wrap_num(t)} :=
  (Nat.choose_eq_descFactorial_div_factorial {N} {K}).trans (by decide +kernel)

{rec_opt}/-- Column certificates for `C({N}, {K})`, columns `k = 2, …, {km}`. -/
def cert_{N}_{K} : List ℕ :=
{wrap(as_, indent="  ")}

{hb_opt}/-- The Lind–Singmaster number for `i = {i}`, `C({N}, {K}) = C({N - 1}, {K + 1})` ({digits} digits),
appears exactly six times in Pascal's triangle. -/
theorem ncard_choose_{N}_{K} : (solutions (({N} : ℕ).choose {K})).ncard = 6 := by
  rw [choose_{N}_{K}]
  exact (ncard_eq_of_certOK (S := [({N}, {K}), ({N - 1}, {K + 1})]) (as := cert_{N}_{K})
    (by norm_num) (by decide +kernel)).trans (by decide)

/-- The same statement in the form of `Singmaster.choose_fib_eq` with `i = {i}`. -/
theorem ncard_solutions_fib_{i} :
    (solutions ((fib {2 * i + 2} * fib {2 * i + 3}).choose
      (fib {2 * i} * fib {2 * i + 3}))).ncard = 6 := by
  have h1 : fib {2 * i + 2} * fib {2 * i + 3} = {N} := by decide
  have h2 : fib {2 * i} * fib {2 * i + 3} = {K} := by decide
  rw [h1, h2]
  exact ncard_choose_{N}_{K}
""")
col.append("end Singmaster\n")
open(f"{OUT}/Collisions.lean", "w").write("\n".join(col))

# Central
ent = []
for m in range(2, M + 1):
    t = comb(2 * m, m)
    km, as_, found = cert(t, [(2 * m, m)])
    assert km == m and len(as_) == m - 1 and not found
    ent.append(f"  ({t},\n{wrap(as_, indent='    ')})")
cen = [HEADER, f"""import Singmaster.Certified
import Singmaster.Parity

/-!
# Central binomial coefficients up to `C({2 * M}, {M})`

For `2 ≤ m ≤ {M}`, the kernel checks that `C(2m, m)` appears only at `(2m, m)`, `(t, 1)` and
`(t, t - 1)`, so it appears exactly three times. Together with
`Singmaster.exists_centralBinom_of_odd_ncard`, no number below `C({2 * M + 2}, {M + 1})`
(about `10^{len(str(comb(2 * M + 2, M + 1))) - 1}`) appears exactly 5 or 7 times.
-/

namespace Singmaster

/-- The check for `m = m₀, m₀ + 1, …`. Each entry `(t, as)` has `t = C(2m, m)`, checked as
`(2m)(2m - 1) ⋯ (m + 1) = m! t`, and column certificates `as` for `k = 2, …, m` in which
`(2m, m)` is the only listed position. -/
def centralOK : ℕ → List (ℕ × List ℕ) → Bool
  | _, [] => true
  | m, (t, as) :: rest =>
    decide ((2 * m).descFactorial m = m.factorial * t) && decide (as.length + 1 = m) &&
      colsOK t [(2 * m, m)] 2 as && centralOK (m + 1) rest

theorem centralBinom_lt_succ (m : ℕ) : Nat.centralBinom m < Nat.centralBinom (m + 1) := by
  have h := Nat.succ_mul_centralBinom_succ m
  have hp := Nat.centralBinom_pos m
  have h2 : (m + 1) * Nat.centralBinom m < (m + 1) * Nat.centralBinom (m + 1) := by
    rw [h]
    nlinarith
  exact Nat.lt_of_mul_lt_mul_left h2

theorem centralBinom_strictMono : StrictMono Nat.centralBinom :=
  strictMono_nat_of_lt_succ centralBinom_lt_succ

theorem centralOK_sound (L : List (ℕ × List ℕ)) :
    ∀ m₀, centralOK m₀ L = true → ∀ m, m₀ ≤ m → m < m₀ + L.length →
      ∀ n k, 2 ≤ k → 2 * k ≤ n → n.choose k = Nat.centralBinom m → n = 2 * m ∧ k = m := by
  induction L with
  | nil =>
    intro m₀ _ m h1 h2
    simp only [List.length_nil, Nat.add_zero] at h2
    omega
  | cons e L ih =>
    obtain ⟨t, as⟩ := e
    intro m₀ h m h1 h2 n k hk hkn hn
    simp only [centralOK, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨ht, hlen⟩, hcols⟩, hrest⟩ := h
    rcases Nat.eq_or_lt_of_le h1 with rfl | h1'
    · have ht' : t = Nat.centralBinom m₀ := by
        rw [Nat.descFactorial_eq_factorial_mul_choose] at ht
        rw [Nat.centralBinom_eq_two_mul_choose]
        exact (Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos _) ht).symm
      subst ht'
      have htop : Nat.centralBinom m₀ < (2 * (as.length + 2)).choose (as.length + 2) := by
        rw [show as.length + 2 = m₀ + 1 by omega, ← Nat.centralBinom_eq_two_mul_choose]
        exact centralBinom_lt_succ m₀
      have hmem := mem_of_colsOK hcols htop hk hkn hn
      simpa using hmem
    · simp only [List.length_cons] at h2
      exact ih (m₀ + 1) hrest m (by omega) (by omega) n k hk hkn hn

/-- If `(2m, m)` is the only position `(n, k)` of `C(2m, m)` with `2 ≤ k` and `2k ≤ n`, then
`C(2m, m)` appears exactly three times. -/
theorem ncard_centralBinom_of_unique {{m : ℕ}} (hm : 2 ≤ m)
    (hu : ∀ n k, 2 ≤ k → 2 * k ≤ n → n.choose k = Nat.centralBinom m → n = 2 * m ∧ k = m) :
    (solutions (Nat.centralBinom m)).ncard = 3 := by
  have hc : 2 * m < Nat.centralBinom m := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    exact lt_choose hm (by omega)
  have hS : solutions (Nat.centralBinom m) =
      {{(Nat.centralBinom m, 1), (Nat.centralBinom m, Nat.centralBinom m - 1), (2 * m, m)}} := by
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
        · exact hu n k hk2 hhalf h
        · have hsym : n.choose (n - k) = Nat.centralBinom m :=
            (Nat.choose_symm (by omega)).trans h
          have := hu n (n - k) (by omega) (by omega) hsym
          exfalso
          omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨le_rfl, by omega, Nat.choose_one_right _⟩
      · exact ⟨by omega, by omega,
          (Nat.choose_symm_of_eq_add (by omega)).trans (Nat.choose_one_right _)⟩
      · exact ⟨by omega, by omega, (Nat.centralBinom_eq_two_mul_choose _).symm⟩
  rw [hS]
  refine Set.ncard_eq_three.2 ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;>
    simp only [ne_eq, Prod.mk.injEq, not_and] <;> omega

/-- `2 = C(2, 1)` appears once. -/
theorem solutions_two : solutions 2 = {{(2, 1)}} := by
  ext ⟨n, k⟩
  simp only [mem_solutions, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hk, hkn, h⟩
    have := le_choose hk hkn
    omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨le_rfl, by norm_num, Nat.choose_one_right 2⟩

-- The default `maxRecDepth` is too small to elaborate this list.
set_option maxRecDepth 100000 in
/-- Certificates for `m = 2, …, {M}`. -/
def centralCerts : List (ℕ × List ℕ) := [
""" + ",\n".join(ent) + f"""]

theorem centralCerts_length : centralCerts.length = {M - 1} := by
  decide +kernel

theorem centralOK_centralCerts : centralOK 2 centralCerts = true := by
  decide +kernel

/-- For `2 ≤ m ≤ {M}`, `C(2m, m)` appears exactly three times in Pascal's triangle. -/
theorem ncard_centralBinom {{m : ℕ}} (h1 : 2 ≤ m) (h2 : m ≤ {M}) :
    (solutions (Nat.centralBinom m)).ncard = 3 :=
  ncard_centralBinom_of_unique h1
    (centralOK_sound centralCerts 2 centralOK_centralCerts m h1
      (by rw [centralCerts_length]; omega))

/-- **No number below `C({2 * M + 2}, {M + 1})` appears exactly 5 or 7 times** in Pascal's triangle. -/
theorem ncard_ne_five_and_ne_seven {{t : ℕ}} (ht : t < Nat.centralBinom {M + 1}) :
    (solutions t).ncard ≠ 5 ∧ (solutions t).ncard ≠ 7 := by
  suffices h : ¬ ((solutions t).ncard = 5 ∨ (solutions t).ncard = 7) from
    ⟨fun h5 => h (Or.inl h5), fun h7 => h (Or.inr h7)⟩
  intro h57
  obtain ⟨m, hm1, rfl⟩ := exists_centralBinom_of_ncard_eq_five_or_seven h57
  have hm : m ≤ {M} := by
    by_contra hc
    have := centralBinom_strictMono.monotone (show {M + 1} ≤ m by omega)
    omega
  rcases (show m = 1 ∨ 2 ≤ m by omega) with rfl | hm2
  · rw [show Nat.centralBinom 1 = 2 from rfl, solutions_two, Set.ncard_singleton] at h57
    omega
  · rw [ncard_centralBinom hm2 hm] at h57
    omega

end Singmaster
"""]
open(f"{OUT}/Central.lean", "w").write("".join(cen))
print(f"wrote {OUT}/Collisions.lean and {OUT}/Central.lean (M = {M})")
