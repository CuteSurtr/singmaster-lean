# Singmaster's conjecture in Lean 4

[Singmaster's conjecture](https://en.wikipedia.org/wiki/Singmaster%27s_conjecture) (1971) says that
every integer $t > 1$ appears at most a bounded number of times in Pascal's triangle. It is open.

This project proves known facts about it and some new exact counts. All statements use the
definition `Singmaster.solutions` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/Wikipedia/Singmaster.lean`), so `(solutions t).ncard` is the quantity the open
conjecture bounds there. Below, $N(t)$ means `(solutions t).ncard`, the number of positions
$(n, k)$ with $1 \le k < n$ and $\binom{n}{k} = t$.

## Statements

| Lean name | Statement |
| --- | --- |
| `Singmaster.solutions_3003` | The positions of $3003$ are $(3003, 1)$, $(3003, 3002)$, $(78, 2)$, $(78, 76)$, $(15, 5)$, $(15, 10)$, $(14, 6)$, $(14, 8)$. |
| `Singmaster.singmaster.variants.ncard_3003` | $N(3003) = 8$. |
| `Singmaster.eight_le_of_bound` | Any uniform bound in Singmaster's conjecture is at least $8$. |
| `Singmaster.choose_fib_eq` | $\binom{F_{2i+2}F_{2i+3}}{F_{2i}F_{2i+3}} = \binom{F_{2i+2}F_{2i+3}-1}{F_{2i}F_{2i+3}+1}$ for every $i$ (Lind 1968, Singmaster 1975). |
| `Singmaster.six_le_ncard_solutions_fib` | For $i \ge 1$ that common value appears at least $6$ times. |
| `Singmaster.singmaster.variants.infinite_six_le_ncard` | Infinitely many integers appear at least $6$ times. |
| `Singmaster.choose_eq_choose_pred_succ_iff_fib` | Conversely, for $1 \le k$ and $k + 2 \le n$, $\binom{n}{k} = \binom{n-1}{k+1}$ only for $n = F_{2i+2}F_{2i+3}$, $k = F_{2i}F_{2i+3}$ (Lind 1968). |
| `Singmaster.ncard_prime`, `Singmaster.singmaster.variants.infinite_ncard_eq_two` | A prime $p \ge 3$ appears exactly $2$ times, so infinitely many numbers do. |
| `Singmaster.ncard_choose_prime_two`, `Singmaster.singmaster.variants.infinite_ncard_eq_four` | For a prime $p \ge 5$, $\binom{p}{2}$ appears exactly $4$ times, so infinitely many numbers do. |
| `Singmaster.singmaster.variants.ncard_le_two_mul_log` | $N(t) \le 2 \log_2 t$ for every $t$ (Singmaster 1971). |
| `Singmaster.odd_ncard_iff` | $N(t)$ is odd if and only if $t = \binom{2m}{m}$ for some $m \ge 1$. |
| `Singmaster.exists_centralBinom_of_ncard_eq_five_or_seven` | In particular, a number that appears exactly $5$ or $7$ times is a central binomial coefficient. |
| `Singmaster.ncard_120`, `ncard_210`, `ncard_1540`, `ncard_7140`, `ncard_11628`, `ncard_24310` | Each of $120, 210, 1540, 7140, 11628, 24310$ appears exactly $6$ times. |
| `Singmaster.ncard_choose_104_39` | $\binom{104}{39} = \binom{103}{40}$, a number with 29 digits, appears exactly $6$ times. |
| `Singmaster.ncard_choose_714_272` | $\binom{714}{272} = \binom{713}{273}$, a number with 205 digits, appears exactly $6$ times. |
| `Singmaster.ncard_choose_4895_1869` | $\binom{4895}{1869} = \binom{4894}{1870}$, a number with 1412 digits, appears exactly $6$ times. |
| `Singmaster.ncard_centralBinom` | For $2 \le m \le 200$, $\binom{2m}{m}$ appears exactly $3$ times. |
| `Singmaster.ncard_eq_one_or_three_of_odd`, `Singmaster.ncard_ne_five_and_ne_seven` | A number below $\binom{402}{201} \approx 4.1 \cdot 10^{119}$ that appears an odd number of times appears once or three times; in particular none appears exactly $5$ or $7$ times. |
| `Singmaster.central_window`, `Singmaster.choose_eq_window` | The divisibility rules used to prune computer searches for further positions. |

The numbers $120, \dots, 24310$, $3003$ and the Lind–Singmaster values are all the numbers known
to appear more than four times. The three Lind–Singmaster rows above are the cases $i = 2$, $3$
and $4$ of `choose_fib_eq`.

## Proof outlines

$N(3003) = 8$: rows of Pascal's triangle are unimodal, so an entry with $2 \le k \le n - 2$ is at
least $\binom{n}{2}$. Then $\binom{n}{k} = 3003$ forces $n \le 78$, and the kernel checks the rows
$n \le 78$ with `decide +kernel`, computing $\binom{n}{k}$ as $n^{\underline{k}} / k!$.

The Lind–Singmaster family: with $a = F_{2i}$ and $b = F_{2i+1}$, Cassini's identity gives
$b^2 = ab + a^2 + 1$. That makes $n = (a+b)(a+2b)$ and $k = a(a+2b)$ satisfy
$n(k+1) = (n-k)(n-k-1)$, which is equivalent to $\binom{n}{k} = \binom{n-1}{k+1}$.

Lind's theorem: with $s = k + 1$ and $c = n - 2k - 1$, the collision becomes
$s^2 + c = sc + c^2$. A gcd argument gives $c = b^2$ and $s = b(a+b)$ with $b^2 = ab + a^2 + 1$,
and descent $(a, b) \mapsto (2a - b, b - a)$ shows $a = F_{2i}$, $b = F_{2i+1}$.

Odd multiplicities: the positions $(n, k)$ and $(n, n - k)$ pair up, and a position is its own
partner only when $n = 2k$.

Exact counts (`Singmaster/Certified.lean`): it suffices to find the positions with $2 \le k$ and
$2k \le n$. Column $k$ increases with $n$, so a row $a$ with
$\binom{a}{k} < t < \binom{a+1}{k}$ certifies that $t$ is not in column $k$, and a column with
$\binom{2k}{k} > t$ cannot contain $t$ there. The kernel checks one such certificate per column
by comparing $k!\,t$ with $a(a-1)\cdots(a-k+1)$, so it never divides. The certificates are
generated by `scripts/certificates.py`. The script is not trusted: a wrong certificate fails the
check. Combined with the odd-multiplicity theorem, the central check for $m \le 200$ rules out
multiplicities $5$ and $7$ below $\binom{402}{201}$.

## Files

| File | Contents |
| --- | --- |
| `Singmaster/Basic.lean` | The definition, unimodality of rows, and finiteness of `solutions t`. |
| `Singmaster/N3003.lean` | $N(3003) = 8$. |
| `Singmaster/Fibonacci.lean` | The Lind–Singmaster family. |
| `Singmaster/Adjacent.lean` | Lind's theorem: every collision between adjacent rows is in that family. |
| `Singmaster/LogBound.lean` | Singmaster's bound $N(t) \le 2 \log_2 t$. |
| `Singmaster/Parity.lean` | $N(t)$ is odd exactly for central binomial coefficients. |
| `Singmaster/Primes.lean` | Numbers that appear exactly twice or four times. |
| `Singmaster/Window.lean` | The bracket $(n+1-k)^k \le k! \binom{n}{k} \le n^k$ and the prime-window rules. |
| `Singmaster/Certified.lean` | Column certificates, their soundness, and exact counts from a passing check. |
| `Singmaster/Collisions.lean` | Exact counts for the known repeated numbers (generated). |
| `Singmaster/Central.lean` | $\binom{2m}{m}$ for $2 \le m \le 200$, and no multiplicity $5$ or $7$ below $\binom{402}{201}$ (generated). |
| `scripts/certificates.py` | Regenerates `Collisions.lean` and `Central.lean`. |
| `Audit.lean` | Fails the build if a listed result uses an axiom other than `propext`, `Classical.choice` and `Quot.sound`. |

No file uses `sorry` or `native_decide`.

## Checking

GitHub Actions runs `lake build --wfail` with Lean and Mathlib v4.34.0 on every push. That builds
`Singmaster` and `Audit`, so a warning, an error or a nonstandard axiom fails the check. To build
locally:

```bash
lake exe cache get && lake build
```

The files were also checked on [live.lean-lang.org](https://live.lean-lang.org): `Basic`, `N3003`,
`Fibonacci` and `LogBound` on 2026-10-12 with v4.34.0, and `Parity`, `Adjacent`, `Primes`,
`Window`, `Certified`, `Collisions` and `Central` on 2026-10-25 with v4.35.0. Both times there were no errors or warnings,
and `#print axioms` reported only `propext`, `Classical.choice` and `Quot.sound`.

## References

- D. Singmaster, *How often does an integer occur as a binomial coefficient?*, Amer. Math. Monthly
  78 (1971), 385-386.
- D. A. Lind, *The quadratic field Q(√5) and a certain Diophantine equation*, Fibonacci Quart. 6
  (1968), 86-93.
- D. Singmaster, *Repeated binomial coefficients and Fibonacci numbers*, Fibonacci Quart. 13 (1975),
  295-298.
- C. A. Tovey, *Multiple occurrences of binomial coefficients*, Fibonacci Quart. 23 (1985), 356-358.
- A. Blokhuis, A. Brouwer and B. de Weger, *Binomial collisions and near collisions*, Integers 17
  (2017), A64.
