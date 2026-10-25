# Searches related to Singmaster's conjecture

`singsearch.py` looks for representations t = C(n, k) with k >= 2 of two kinds of numbers:

- **Central binomial coefficients** t = C(2m, m), with 2 <= k < m. Positions of t in Pascal's
  triangle pair up as (n, k) and (n, n - k), except the middle entry of an even row, so a number
  appears an odd number of times only if it is C(2m, m). If C(2m, m) has no representation with
  2 <= k < m for all m <= M, no number below C(2M + 2, M + 1) appears exactly 5 or 7 times
  (or any odd number of times other than 1 and 3).
- **Members of the Lind–Singmaster family** t = C(F(2i+2) F(2i+3), F(2i) F(2i+3)), which appear
  at least six times. A third representation with k >= 2 would make t appear at least eight times.

For each k, a solution n lies in [x, x + k - 1] with x = floor((k! t)^(1/k)); the bracket is
computed exactly, or with correctly rounded MPFR arithmetic and a safety margin. Candidates are
discarded with p-adic valuations: for a prime p > k, the window (n - k, n] must contain a
multiple of p exactly when p divides t. A second filter removes every candidate whose window
contains a prime P > k with P not dividing t (all prime factors of t are at most a known B;
primes above B are certified with Miller-Rabin to the first 13 prime bases, which is
deterministic below 3.3 * 10^24). Survivors are checked exactly. `selftest` compares the filtered
search with an unfiltered exact search and recovers all known collisions.

The workflow in `.github/workflows/search.yml` runs the searches on GitHub Actions and merges
the results into `report.json`.
