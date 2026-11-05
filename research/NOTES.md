# Research log, 2026-10-12

Goal: find something new about Singmaster's conjecture, without running heavy jobs locally (the
machine was busy with ES(8) proofs). Lean was checked on live.lean-lang.org and the searches
ran on GitHub Actions.

## Literature check

- Exhaustive searches: Blokhuis, Brouwer and de Weger (2017) found no collisions beyond the known
  ones for n ≤ 10^6 or values ≤ 10^60. OEIS A003015 cites a 2026 sieve by M. Ramirez reaching
  10^62 (not independently found).
- Erdős Problem #849 (erdosproblems.com/849) is the same question, counting k ≤ n/2. Open; no
  number with ≥ 5 such representations is known.
- No source found that searches central binomial coefficients C(2m, m) for extra
  representations, or that checks Lind–Singmaster family members beyond i = 2 for a third
  representation.

## Results so far

### 1. Lind–Singmaster members i = 3, 4, 5, 6 appear exactly 6 times (complete)

For t = C(F(2i+2) F(2i+3), F(2i) F(2i+3)), the search covered every k from 2 to kmax, where
C(2k, k) ≤ t holds for every k ≤ n/2. It found only the two known positions each time.

| i | (N, K) | digits of t | k searched | positions with 2 ≤ k ≤ n/2 |
| --- | --- | --- | --- | --- |
| 3 | (714, 272) | 205 | 2..350 | (714, 272), (713, 273) |
| 4 | (4895, 1869) | 1,412 | 2..2355 | (4895, 1869), (4894, 1870) |
| 5 | (33552, 12815) | 9,688 | 2..16102 | (33552, 12815), (33551, 12816) |
| 6 | (229970, 87840) | 66,416 | 2..110324 | (229970, 87840), (229969, 87841) |

So N(t) = 6 exactly for these four numbers. Data: `search/results/`. All four values are far
beyond the 10^62 range of the published searches.

### 2. Central binomial coefficients: no extra representation for m ≤ 35,273 (complete)

GitHub Actions run 38251669680 (branch `search`) finished successfully. It checked every m from
2 to 35,273 with no gaps, plus 2,654 further values above that, for 37,927 values in all. It
found **no** representation C(2m, m) = C(n, k) with 2 ≤ k < m. A number appears an odd number of
times only if it is C(2m, m) (see `drafts/Parity.lean`). So **no integer t < C(70548, 35274) ≈
10^21234 appears exactly 5 or 7 times** (or any odd number of times ≥ 5). The previous published
range was about 10^62. Report: `search/results/run-38251669680/report.json`.

The same run covered Lind i = 7 (455,237 digits) for k ≤ 163,761 of 756,142, with no extra
representation in that range. This part is incomplete.

## Method (`search/singsearch.py`)

For fixed k, a solution n of C(n, k) = t lies in [x, x + k - 1] with x = floor((k! t)^(1/k)). For
large k the bracket comes from a 60-digit (or `--dps`) mpmath logarithm, widened by a safe margin.
Candidates are discarded with p-adic valuations for primes p > k. The window (n - k, n] contains
a multiple of p exactly when p | t, with v_p(t) from Kummer's theorem. Survivors are checked
exactly. `selftest` compares the filter with an unfiltered exact search, recovers every known
collision, and recovers both known positions of the Lind members i = 1..4.

## Literature

`LITERATURE.md` (2026-10-14, second pass): about 75 annotated references, a table placing our
results against prior work, and the Mathlib lemmas needed to formalize the search's valuation
filter. Key framing: de Weger's Conjecture A (1997); Tovey's 1985 conjecture; Clark 2010 as a
formalization target.

## Lean

- `Singmaster/LogBound.lean` (new, wired into `Singmaster.lean` and `Audit.lean`):
  `singmaster.variants.ncard_le_two_mul_log : (solutions t).ncard ≤ 2 * Nat.log 2 t`, which is
  Singmaster's 1971 bound. Checked on live.lean-lang.org with Lean and Mathlib v4.34.0, together
  with `Basic.lean`: no errors, axioms `propext`, `Classical.choice`, `Quot.sound`. Not yet run
  through `lake build` or CI. Not committed.
- `drafts/Parity.lean` (unchecked): odd N(t) implies t = C(2m, m), and so does N(t) ∈ {5, 7}.
  It was written but never compiled, and it is not imported by the library. Check it before
  moving it into `Singmaster/`.

## Tools

- `tools/lzurl.py SRC PROJECT OUT`: builds a live.lean-lang.org URL (`codez=`, LZString base64)
  for a single Lean file. After navigating, reload the page once, then read diagnostics from the
  infoview iframe.

## Next steps

1. Done: central coverage m ≤ 35,273; Lind i = 7 partial (k ≤ 163,761). See LITERATURE.md for how these relate to de Weger's Conjecture A.
2. Compile `drafts/Parity.lean`, then add it to the library.
3. Run `lake build` in CI with LogBound (push when ready).
4. A note combining the results: "N(t) ∉ {5, 7} for t < C(2M + 2, M + 1)" and "the Lind members
   i = 3..6 appear exactly 6 times" seem new. Check the literature once more before claiming that.

# Session 3, 2026-10-25

## Lean (branch `log-bound-parity`, all pushed, CI green on v4.34)

- d85603a: `LogBound.lean` and `Parity.lean` in the library. CI run 40167286862 passed.
- 6ab4db4: `Window.lean`, `Certified.lean`, `Collisions.lean`, `Central.lean`,
  `scripts/certificates.py`. CI run 40169273551 passed. The whole library was also checked as one
  file on live.lean-lang.org with v4.35.0: no errors or warnings, 27 audited theorems with only
  `propext`, `Classical.choice`, `Quot.sound`.
- New theorems:
  - `N(t) = 6` exactly for 120, 210, 1540, 7140, 11628, 24310 and for the Lind–Singmaster numbers
    `C(104, 39)` (29 digits) and `C(714, 272)` (205 digits). The 205-digit case is new as a
    result, not only as a formalization: published searches stop at 10^60 and at rows ≤ 10^6.
  - `C(2m, m)` appears exactly 3 times for `2 ≤ m ≤ 200`. With the parity theorem: no number
    below `C(402, 201) ≈ 4.1·10^119` appears exactly 5 or 7 times (kernel-checked).
  - `Window.lean`: the bracket `(n+1-k)^k ≤ k! C(n,k) ≤ n^k` and the prime-window rules used by
    `singsearch.py`.
- Method (`Certified.lean`): for each column k = 2..K-1, a certificate row a with
  C(a,k) < t < C(a+1,k) (or < C(a+2,k) when (a+1,k) is a known position). The kernel compares
  k! t with a(a-1)...(a-k+1), using (a+1-k) C(a+1,k) = (a+1) C(a,k), so it never divides.
  Columns with C(2k,k) > t are excluded by unimodality. Kernel time: about 20 s for m ≤ 100,
  about 2 min for m ≤ 200 on live.lean-lang.org.
- 027ea58: `C(4895, 1869)` (1412 digits) appears exactly 6 times; 425,055 heartbeats
  (`set_option maxHeartbeats 1000000`). CI 40170056622 passed.
- 67ab210: `Adjacent.lean`, Lind's theorem (all solutions of C(n,k) = C(n-1,k+1), k ≥ 1, are
  the Fibonacci family): gcd argument then descent. Compiled first try. CI 40170516334 passed.
- 9bd0786: `Primes.lean`: N(p) = 2 for primes p ≥ 3, N(C(p,2)) = 4 for primes p ≥ 5, so
  {t | N(t) = 2} and {t | N(t) = 4} are infinite.
- 9a9e048: `odd_ncard_iff` (N(t) odd ⟺ t = C(2m, m), m ≥ 1); monotonicity of C(2m, m) moved
  from the generated `Central.lean` into `Parity.lean`.
- 65ca97e: `ncard_eq_one_or_three_of_odd` (below C(402, 201), odd N(t) is 1 or 3).
  Note: pushing a new commit cancels the branch's running CI (concurrency group), so only the
  newest run counts.
- Tovey 1985 read from the scan: his "t = 2" is at least two representations plus Lind's
  theorem; no exactness. So exact N(L_i) = 6 for i = 3, 4 (formal) and up to i = 6 (search)
  stays new. Open-looking: infinitely many t with N(t) = 3? with N(t) = 6?
- Tried a cheaper "divisor witness" certificate (one x in the bracket with x ∤ k! t excludes a
  column with O(1) GMP operations); it works for only about half the columns, so the formal
  range stays at m ≤ 200 and L_4. Prototype: `cert/witness.py`.
- v4.35 renames met: `Prime.dvd_finset_prod_iff` (avoided with an induction),
  `Set.mem_setOf_eq` (avoided with `change`). Big list literals need
  `set_option maxRecDepth 100000 in`.

## Cloud-check method (no long URLs pasted)

`research/tools/lzurl.py` writes the codez URL; a one-line HTML page
`research/tools/go/<name>.html` does `location.replace(url)`. `.claude/launch.json` (in the
ES repo root) has a config `lean-cloud-redirect` serving that folder on port 8765 through the
Browser pane's `preview_start`. Navigate to `http://localhost:8765/<name>.html`, set the viewport
to 1280x800, reload, wait, then read the infoview iframe and click "All Messages".

## Search (orphan branch `search`)

- New `singsearch.py` (b4f4d6a, 115db9b): prime-in-window filter, MPFR brackets, Lind bounds
  nmin/nmax. Copied to `search/singsearch.py`; the 2026-10-12 version is `singsearch_v1.py`.
- Run 40166727006 (05:46Z to 10:49Z, all 19 jobs succeeded). Report and per-job JSON in
  `search/results/run-40166727006/` (44 MB):
  - Central: every m from 2 to 150,001 (inclusive) and scattered m up to 205,981, 177,436 values
    in all: no C(2m, m) equals any C(n, k) with 2 ≤ k < m. So a number below
    C(300004, 150002) ≈ 2.3·10^90307 that appears an odd number of times appears once or three
    times; none appears exactly 5 or 7 times. (Previous bound: 10^21234.) 12.8 million exact
    checks, 3.8·10^9 prime tests.
  - L_7 = C(1576239, 602069), 455,237 digits: complete (k = 2..756,142). Hits only at the two
    known positions (602069, 1576239) and (602070, 1576238). So N(L_7) = 6.
  - L_8 = C(10803704, 4126647), 3,120,256 digits: no position with 2 ≤ k ≤ 3,383,345 (65.3% of
    kmax 5,182,642).
  - L_9 = C(74049690, 28284464), 21,386,570 digits: no position with 2 ≤ k ≤ 22,931,135 (64.6%
    of kmax 35,522,333).
  - Runner speeds differ about 2x: the slowest central job reached m ≈ 150,000, the fastest
    205,981. Contiguous coverage is set by the slowest lane.
  - Soundness note: for huge n the bracket uses an exact integer k-th root of k!·t (gmpy2.iroot),
    not the 400-digit logarithm, so no column is skipped for lack of precision.
- Continuation run 40186682964 (started 10:54Z, search branch ddb5f31): `central --mlist
  central_todo.json` (the 34,563 m in 150002..212000 not yet done, 12 jobs) and `lind --kstart`
  (i = 8 from k = 3,383,346 with 2 jobs; i = 9 from k = 22,931,136 with 4 jobs).
  Finished 15:55Z, all jobs succeeded; results in `search/results/run-40186682964/`.
  - Central: all 34,563 values done, no hits. Combined with the first run: **every m from 2 to
    212,000**, no C(2m, m) equals any C(n, k) with 2 ≤ k < m. Bound:
    C(424002, 212001) ≈ 2.6·10^127634. Below it, odd multiplicities are 1 or 3; none is 5 or 7.
  - Lind i = 8 advanced only to k = 3,500,970, i = 9 only to k = 22,989,519 (50 to 400 times
    slower than before).
- **Stall diagnosis.** For N/(2φ) ≤ k < K (k/N = 0.30902 for both i = 8 and 9; for i = 7 the
  33,286 heavy columns are exactly this range, none above K) every column hit the 400-prime cap
  and kept g − 1 candidates, where g is the gap from N to the next prime (6 for i = 8, 2 for
  i = 9, 1 for i = 7). Those are n ∈ (N, nextprime(N)): no prime above N in their window, no
  prime ∤ t either (all primes in (0.618N, N] divide t), and the primes dividing t that would
  remove them lie in (0.618N, N − k], while the filter tries primes dividing t from the top down.
  Each survivor cost an exact C(n, k) with millions of digits. Why 1/(2φ): at k = (N − K)/2 the
  window (n − k, n] starts to sit above N − K.
- **Fix** (search branch 6830d82): `gap_kill` drops a candidate interval [n_lo, n_hi] when some
  prime p > k dividing t satisfies p > n_hi, or max(k, n_hi/2) < p ≤ n_lo − k (then no multiple
  of p lies in any window). On 64 stalled columns of i = 7: exact checks 64 → 0, primes tried
  25,600 → 768. Selftest passes; the known i = 7 positions are still found.
- Third run 40209681608 (16:01Z to 16:04Z): i = 8 from k = 3,500,971 (8 lanes), i = 9 from
  k = 22,989,520 (48 lanes). Every assigned column finished in about a minute (above K a prime
  dividing t exceeds every candidate; between N/(2φ) and K the gap test removes the near-N
  candidates). Hits: exactly the known positions, (4126647, 10803704) and (4126648, 10803703)
  for i = 8, (28284464, 74049690) and (28284465, 74049689) for i = 9. Results in
  `search/results/run-40209681608/`.
- **Combined Lind result:** k = 2..kmax covered for i = 8 (runs 1-3: ≤ 3,383,345; to 3,500,970;
  to 5,182,642) and i = 9 (≤ 22,931,135; to 22,989,519; to 35,522,333). So L_8 (3,120,256
  digits) and L_9 (21,386,570 digits) appear exactly six times, like L_3, ..., L_7.
- A redundant run triggered by a README-only push to `search` (40210243543) was cancelled; the
  workflow runs on every push to that branch.
- Next possible step: L_10 (N = 507,544,127, about 146.6 million digits). The bulk is
  k < N/(2φ) ≈ 157 million columns at about 80 columns/s per lane, roughly 10 hours on 56 lanes,
  and the prime lists up to N need about 1 GB per worker. Not started.
