# Exact multiplicities in Pascal's triangle: certified counts and a search for odd multiplicities

Draft, 2026-10-25. Repository: github.com/CuteSurtr/singmaster-lean (branch `log-bound-parity`
for the Lean results, orphan branch `search` for the search code and workflows).

## Setting

For an integer t ≥ 2 let N(t) be the number of positions (n, k), 1 ≤ k ≤ n − 1, with
C(n, k) = t. This is `(Singmaster.solutions t).ncard` in google-deepmind/formal-conjectures.
Singmaster (1971) conjectured that N(t) is bounded. The largest known value is N(3003) = 8. The
numbers known to have N(t) ≥ 5 are 120, 210, 1540, 3003, 7140, 11628, 24310 and the
Lind–Singmaster numbers L_i = C(F(2i+2) F(2i+3), F(2i) F(2i+3)), i ≥ 1 (L_1 = 3003). It is
unknown whether any number appears exactly 5 or exactly 7 times.

de Weger's Conjecture A (1997) says the known collisions are all of them. It implies N(L_i) = 6
for i ≥ 2 and that no number appears 5 or 7 times.

## Results

### Machine-checked (Lean 4 and Mathlib; CI on v4.34.0, also checked on v4.35.0)

All of these depend only on the axioms `propext`, `Classical.choice` and `Quot.sound`. No
`sorry`, no `native_decide`; the finite checks use `decide +kernel`.

1. N(t) = 6 exactly for t = 120, 210, 1540, 7140, 11628, 24310, and for L_2 = C(104, 39)
   (29 digits), L_3 = C(714, 272) (205 digits) and L_4 = C(4895, 1869) (1412 digits).
   N(3003) = 8.
2. For 2 ≤ m ≤ 200, N(C(2m, m)) = 3.
3. N(t) is odd if and only if t = C(2m, m) for some m ≥ 1.
4. From 2 and 3: a number t < C(402, 201) ≈ 4.1·10^119 with N(t) odd has N(t) ∈ {1, 3}; in
   particular none appears exactly 5 or 7 times.
5. Lind's theorem: for 1 ≤ k, k + 2 ≤ n, C(n, k) = C(n − 1, k + 1) iff n = F(2i+2) F(2i+3),
   k = F(2i) F(2i+3) for some i ≥ 1.
6. N(t) ≤ 2 log₂ t (Singmaster 1971); infinitely many t have N(t) ≥ 6.
7. A prime p ≥ 3 appears exactly twice and C(p, 2) for a prime p ≥ 5 appears exactly four
   times; so N(t) = 2 and N(t) = 4 each hold for infinitely many t (Tovey's conjecture for 0 and
   1 proper representations).

Items 1 (for L_3 and L_4), 2 and 4 are new as results that can be checked by a proof checker.
The values L_3 and L_4 lie far beyond the published exhaustive searches (values ≤ 10^60, rows
≤ 10^6, Blokhuis–Brouwer–de Weger 2017). We found no earlier formalization of items 1, 2, 4
and 5.

### Computational (GitHub Actions; not machine-checked)

8. Central binomial coefficients: no C(2m, m) with 2 ≤ m ≤ 212,000 equals any C(n, k) with
   2 ≤ k < m (runs 40166727006 and 40186682964). Hence a number below
   C(424002, 212001) ≈ 2.6·10^127634 that appears an odd number of times appears once or three
   times, and none appears exactly 5 or 7 times.
9. Lind–Singmaster numbers: L_3, …, L_9 appear exactly 6 times. All k with C(2k, k) ≤ t were
   searched and only the two known positions turn up. L_9 = C(74049690, 28284464) has
   21,386,570 digits.

## Methods

**Column certificates (Lean, `Certified.lean`).** It suffices to find the positions with
2 ≤ k and 2k ≤ n; the others are (t, 1), (t, t − 1) and the mirror images. Column k increases
with n, so a row a with C(a, k) < t < C(a + 1, k) shows that t is not in column k, and
C(a, k) < t < C(a + 2, k) shows that a + 1 is the only candidate row. Columns with
C(2k, k) > t cannot contain t at a position with 2k ≤ n. The kernel checks one certificate per
column by comparing k!·t with a(a − 1)⋯(a − k + 1) = k!·C(a, k), using
(a + 1 − k)·C(a + 1, k) = (a + 1)·C(a, k) for the next rows, so it never divides. The cost is
about k multiplications per column, so about K²/2 for a number whose last column is K:

| t | digits | columns | kernel time (live.lean-lang.org) |
| --- | --- | --- | --- |
| L_3 = C(714, 272) | 205 | 2..342 | seconds |
| L_4 = C(4895, 1869) | 1412 | 2..2347 | about 3 min, 425,055 heartbeats |
| C(2m, m), 2 ≤ m ≤ 100 | up to 60 | 2..m each | about 20 s |
| C(2m, m), 2 ≤ m ≤ 200 | up to 120 | 2..m each | about 2 min |

The certificates come from `scripts/certificates.py`, which is not trusted.

**A stall and its fix.** For N/(2φ) ≤ k < K the Lind searches slowed by a factor of 50 to
400. The rows n just above N, below the next prime, survive the window filter, and each needed
an exact binomial with millions of digits. A prime p > k dividing t with
max(k, n_max/2) < p ≤ n_min − k has no multiple in any of their windows, so it excludes them
all; primes dividing C(N, K) fill (N − K, N], so such p exist just below N − k. The threshold
is k = (N − K)/2 ≈ N/(2φ), where the windows start to sit above N − K.

**Search (`singsearch.py`).** For fixed k, a solution n of C(n, k) = t lies in a window of k
consecutive integers determined by (k!·t)^(1/k), since (n + 1 − k)^k ≤ k!·C(n, k) ≤ n^k
(`Window.lean`). Candidates are discarded with two divisibility rules, both proved in
`Window.lean`: for a prime p > k, p divides C(n, k) iff p divides one of n, n − 1, …, n − k + 1;
and for t = C(N, K), no prime above N divides t. So a prime p > k that does not divide t must not
divide any number in the window, and every prime p > k that divides t must divide one of them.
For the central case t = C(2m, m), every prime in (m, 2m] divides t and no prime above 2m does.
Survivors are checked exactly.

## Heuristic

Near t, column k ≥ 2 has gaps of about t·k/n with n ≈ (k!·t)^(1/k). So a random integer near t
lies in column k with probability about n/(k·t), and the k = 2 term, about (2t)^(−1/2),
dominates. For t = C(2m, m) ≈ 4^m/√(πm) this is about 2^(−m). The expected number of central
collisions with m > M is therefore about 2^(−M), and the same estimate makes extra
representations of L_i, i ≥ 2, very unlikely. This matches Conjecture A.

## Relation to prior work

- Blokhuis, Brouwer and de Weger (2017): all collisions with value ≤ 10^60 or row ≤ 10^6.
- Matomäki, Radziwiłł, Shao, Tao and Teräväinen (2022): for t large enough (depending on ε),
  at most four solutions with exp((log n)^(2/3+ε)) ≤ k ≤ n − exp((log n)^(2/3+ε)), at most two
  in each half of the triangle. The threshold is not explicit, and small k is not covered.
- Yamada (2020): in the central case the other row must exceed
  2m + m(1.3132 log₂(2m) − 2.00271).
- Tovey (1985): conjectures that for every r infinitely many integers have exactly r proper
  representations; constructs the Fibonacci family (at least two) and proves Lind's theorem, but
  does not prove exactness. Erdős Problem #849 asks the same with 1 ≤ k ≤ n/2. Our parity
  theorem shows that multiplicity 5 or 7 needs a central binomial coefficient. Whether
  infinitely many t have N(t) = 3 (central binomial coefficients with no other representation)
  or N(t) = 6 appears to be open.
- Unverified 2026 claims of a full resolution (Zenodo 21660302; a closed prize claim) do not
  treat exact multiplicities.

## Reproducing

- Lean: `lake exe cache get && lake build` in the repository (builds `Singmaster` and `Audit`).
- Certificates: `python3 scripts/certificates.py 200`.
- Search: workflow `search.yml` on the `search` branch; `python singsearch.py selftest`.
