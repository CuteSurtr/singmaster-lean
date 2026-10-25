# Singmaster's conjecture: two solved cases in Lean 4

[Singmaster's conjecture](https://en.wikipedia.org/wiki/Singmaster%27s_conjecture) (1971) says that
every integer $t > 1$ appears at most a bounded number of times in Pascal's triangle. It is open.

This project proves two known facts about it. Both use the definition `Singmaster.solutions` from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/Wikipedia/Singmaster.lean`), so `(solutions t).ncard` is the quantity the open
conjecture bounds there.

## Statements

| Lean name | Statement |
| --- | --- |
| `Singmaster.solutions_3003` | The positions of $3003$ are $(3003, 1)$, $(3003, 3002)$, $(78, 2)$, $(78, 76)$, $(15, 5)$, $(15, 10)$, $(14, 6)$, $(14, 8)$. |
| `Singmaster.singmaster.variants.ncard_3003` | $N(3003) = 8$. |
| `Singmaster.eight_le_of_bound` | Any uniform bound in Singmaster's conjecture is at least $8$. |
| `Singmaster.choose_fib_eq` | $\binom{F_{2i+2}F_{2i+3}}{F_{2i}F_{2i+3}} = \binom{F_{2i+2}F_{2i+3}-1}{F_{2i}F_{2i+3}+1}$ for every $i$ (Lind 1968, Singmaster 1975). |
| `Singmaster.six_le_ncard_solutions_fib` | For $i \ge 1$ that common value appears at least $6$ times. |
| `Singmaster.singmaster.variants.infinite_six_le_ncard` | Infinitely many integers appear at least $6$ times. |
| `Singmaster.singmaster.variants.ncard_le_two_mul_log` | $N(t) \le 2 \log_2 t$ for every $t$ (Singmaster 1971). |
| `Singmaster.exists_centralBinom_of_odd_ncard` | If $N(t)$ is odd, then $t = \binom{2m}{m}$ for some $m \ge 1$. |
| `Singmaster.exists_centralBinom_of_ncard_eq_five_or_seven` | In particular, a number that appears exactly $5$ or $7$ times is a central binomial coefficient. |

Proof outline for $N(3003) = 8$: rows of Pascal's triangle are unimodal, so an entry with
$2 \le k \le n - 2$ is at least $\binom{n}{2}$. Then $\binom{n}{k} = 3003$ forces $n \le 78$, and the kernel
checks the rows $n \le 78$ with `decide +kernel`, computing $\binom{n}{k}$ as $n^{\underline{k}} / k!$.

Proof outline for the family: with $a = F_{2i}$ and $b = F_{2i+1}$, Cassini's identity gives
$b^2 = ab + a^2 + 1$. That makes $n = (a+b)(a+2b)$ and $k = a(a+2b)$ satisfy
$n(k+1) = (n-k)(n-k-1)$, which is equivalent to $\binom{n}{k} = \binom{n-1}{k+1}$.

## Files

| File | Contents |
| --- | --- |
| `Singmaster/Basic.lean` | The definition, unimodality of rows, and finiteness of `solutions t`. |
| `Singmaster/N3003.lean` | $N(3003) = 8$. |
| `Singmaster/Fibonacci.lean` | The Lind–Singmaster family. |
| `Singmaster/LogBound.lean` | Singmaster's bound $N(t) \le 2 \log_2 t$. |
| `Singmaster/Parity.lean` | Odd multiplicities come from central binomial coefficients. |
| `Audit.lean` | Fails the build if a listed result uses an axiom other than `propext`, `Classical.choice` and `Quot.sound`. |

No file uses `sorry` or `native_decide`.

## Checking

The files were checked on 2026-10-12 on [live.lean-lang.org](https://live.lean-lang.org), project
"Stable Release (v4.34.0 with mathlib)", as one concatenated file: no errors and no warnings. Lean
reported these axioms:

| Declaration | Axioms |
| --- | --- |
| `small_rows_3003` | `propext`, `Quot.sound` |
| `singmaster.variants.ncard_3003` | `propext`, `Classical.choice`, `Quot.sound` |
| `choose_fib_eq` | `propext`, `Classical.choice`, `Quot.sound` |
| `singmaster.variants.infinite_six_le_ncard` | `propext`, `Classical.choice`, `Quot.sound` |

GitHub Actions runs `lake build --wfail` on every push, which builds `Singmaster` and `Audit`.
To build locally:

```bash
lake exe cache get && lake build
```

## References

- D. Singmaster, *How often does an integer occur as a binomial coefficient?*, Amer. Math. Monthly
  78 (1971), 385-386.
- D. A. Lind, *The quadratic field Q(√5) and a certain Diophantine equation*, Fibonacci Quart. 6
  (1968), 86-93.
- D. Singmaster, *Repeated binomial coefficients and Fibonacci numbers*, Fibonacci Quart. 13 (1975),
  295-298.
