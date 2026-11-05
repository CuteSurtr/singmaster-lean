# Literature related to our Singmaster work

Compiled 2026-10-14 (second pass; the first pass had 25 entries, this one about 75). Sources
searched: web search, Semantic Scholar citation graphs of the ten central papers, zbMATH Open
reviews, OEIS, erdosproblems.com. Items marked ⚠ have bibliographic data I could not verify
against the paper itself.

Notation: N(t) counts positions (n, k), 1 ≤ k ≤ n − 1, with C(n, k) = t.

## 1. How our results sit in the literature

| Our result | Closest prior work | Assessment |
| --- | --- | --- |
| Lind–Singmaster members i = 3, …, 9 (205 to 21,386,570 digits) appear exactly 6 times (runs 38251669680, 40166727006, 40186682964, 40209681608) (search over all k; BBdW's n ≤ 10^6 search already covers rows ≤ 10^6 for these, see §11) | de Weger's Conjecture A (1995/1997) predicts exactly this. Searches by value: Singmaster 1975 to 2^48; de Weger 1997 to 10^30 (rows ≤ 1000); Blokhuis–Brouwer–de Weger 2017 to 10^60 (rows ≤ 10^6); OEIS A003015 cites Ramirez (2026) to 10^62. OEIS A098565 lists these numbers as "occurring exactly 6 times" without any proof or bound. | Consistent with Conjecture A; extends the verified range for these numbers. Not found in any source. |
| No C(2m, m), 2 ≤ m ≤ 212,000 (runs 40166727006 and 40186682964; 35,273 in the 2026-10-12 run), equals any C(n, k) with 2 ≤ k < m; so no t < C(424002, 212001) ≈ 2.6·10^127634 appears exactly 5 or 7 times. (Theoretical context: Yamada 2020 shows the other row would have to exceed 2m + m(1.3132 log₂(2m) − 2.00271), see §11.) | Tovey 1985 and Erdős #849 ask about exact multiplicities; OEIS A003015 says "it may be" no number appears exactly 5 times. The only prior central-coefficient equation results are about quotients (Bang–Fuglede 1990) and divisibility, not equality. | Appears new. |
| Lean: N(3003) = 8; Lind identity; infinitely many t with N(t) ≥ 6; N(t) ≤ 2 log₂ t | formal-conjectures has the open statement only. Clark 2010 gives a general "multiplicity of integer arrays" theorem that recovers Singmaster's O(log t). | First formalizations found. Clark's theorem is a natural next formalization target. |
| Lean (checked 2026-10-25): odd N(t) ⇒ t = C(2m, m) | Folklore. | Elementary; formal version new. |
| Lean (2026-10-25): N(t) = 6 exactly for 120, 210, 1540, 7140, 11628, 24310, L_2 = C(104, 39), L_3 = C(714, 272) (205 digits), L_4 = C(4895, 1869) (1412 digits), by kernel-checked column certificates | BBdW 2017 covers values ≤ 10^60 (so the six small numbers and L_2) by unverified computation. | First machine-checked exact counts found; for L_3 and L_4 the counts themselves go beyond published searches. |
| Lean (2026-10-25): N(C(2m, m)) = 3 for 2 ≤ m ≤ 200, so no t < C(402, 201) ≈ 4.1·10^119 appears exactly 5 or 7 times | BBdW 2017 (values ≤ 10^60, unverified computation). | Formal; doubles the exponent of the published range. |
| Lean (2026-10-25): Lind's theorem, C(n, k) = C(n − 1, k + 1) with k ≥ 1 only for the Fibonacci family | Lind 1968; Singmaster 1975. Mathlib's Archive (IMO 1981 Q3) characterizes m² − mn − n² = ±1 but not the binomial statement. | First formalization found. |

## 2. Origins, problem lists, surveys

- **D. Singmaster (1971)**, *How often does an integer occur as a binomial coefficient?*, Amer. Math. Monthly 78, 385–386 (Research Problems column, ed. R. K. Guy). N(t) = O(log t); conjectures N(t) = O(1). 43 citing papers on Semantic Scholar.
- **D. Singmaster (1975)**, *Repeated binomial coefficients and Fibonacci numbers*, Fibonacci Quart. 13, 295–298. The infinite family; searched to 2^48; conjectured N(t) ≤ 10 (per de Weger). https://www.mathstat.dal.ca/FQ/Scanned/13-4/singmaster.pdf
- **D. A. Lind (1968)**, *The quadratic field Q(√5) and a certain Diophantine equation*, Fibonacci Quart. 6, 86–93. Earliest source of the family.
- **C. A. Tovey (1985)**, *Multiple occurrences of binomial coefficients*, Fibonacci Quart. 23(4), 356–358. Rediscovers the family; **conjectures that for every t there are infinitely many integers with exactly t proper representations (1 < k ≤ n/2)** and "proves t = 2" — checked against the scan 2026-10-25: he constructs the Fibonacci family (infinitely many integers with *at least* two proper representations) and proves it gives all solutions of C(n, k) = C(n − 1, k + 1) (his Theorem 2, i.e. Lind's theorem, via 5z² + 4 = y²). He does **not** show that these integers have no further representations, so exact multiplicity 6 of the Lind numbers is not established there. Our central-coefficient result bears on t = 5/2 … i.e. odd total multiplicity. https://www.mathstat.dal.ca/FQ/Scanned/23-4/tovey.pdf
- **P. Erdős, R. L. Graham (1980)**, *Old and new problems and results in combinatorial number theory*, Monographies de L'Enseignement Math. 28. Cites AEH; p. 71 has the C(2n, n)-never-squarefree conjecture.
- **P. Erdős (1996)**, *Some problems I presented or planned to present in my short talk*, in Analytic Number Theory, Vol. 1 (Allerton Park, 1995), 333–335 (zbMATH 903698). Source of Erdős Problem #849 (credited to Erdős–Gordon).
- **Erdős Problem #849**: for every t, is there a with exactly t solutions, 1 ≤ k ≤ n/2? Open; known for t ≤ 4; forum has no posts. https://www.erdosproblems.com/849
- **R. K. Guy**, *Unsolved Problems in Number Theory*, 3rd ed. (2004), §B31 ⚠ (section number from secondary sources).
- **L. Comtet (1974)**, *Advanced Combinatorics*, p. 93 #47; **C. S. Ogilvy (1972)**, *Tomorrow's Math*, p. 96 (OEIS A003016 references).
- **C. Cobeli, A. Zaharescu (2013)**, *Promenade around Pascal triangle — number motives*, Bull. Math. Soc. Sci. Math. Roumanie 56(104), 73–98. Survey; cites Kane 2007. https://rms.unibuc.ro/bulletin/pdf/56-1/PromenadePascalPart1.pdf
- **H. Montanus, R. Westdijk (2022)**, *Cellular Automation and Binomials*, Green Blue Mathematics, p. 69 ⚠ (book; cited on OEIS A003015; content unseen).
- **S. Shahriari (2021)**, *An Invitation to Combinatorics*, CUP. Textbook exercise citing Singmaster 1971.
- **OEIS**: A003016 (N(t)), A003015 (≥ 5 times), A098565 (exactly 6), A098564 (exactly 4), A059233 (rows containing n), A182237, A185024, A090162, A138496, A180058. A003015 cites D. W. Wilson (< 3.3·10^17), M. Ramirez (2026 sieve, < 10^62, nothing with multiplicity > 8) ⚠ not located.
- Popular: Aperiodical "Open Season" (2013); IMA "Frequency of numbers in Pascal's triangle"; Z. Griffiths YouTube (2020); J. D. Cook blog (2016).

## 3. General bounds on N(t)

- **H. L. Abbott, P. Erdős, D. Hanson (1974)**, *On the number of times an integer occurs as a binomial coefficient*, Amer. Math. Monthly 81, 256–261. Average and normal order of N is 2; #{t ≤ x : N(t) > 2} = O(√x); N(t) = O(log t / log log t); O((log t)^{2/3+ε}) under Cramér. https://www.renyi.hu/~p_erdos/1974-23.pdf
- **D. Kane (2004)**, *New bounds on the number of representations of t as a binomial coefficient*, Integers 4, A7. https://emis.univie.ac.at/journals/INTEGERS/papers/e7/e7.pdf
- **D. Kane (2007)**, *Improved bounds on the number of ways of expressing t as a binomial coefficient*, Integers 7, A53. N(t) = O(log t · log log log t / (log log t)^3); best known. https://emis.univie.ac.at/journals/INTEGERS/papers/h53/h53.pdf
- **L. Clark (2010)**, *Multiplicities of integer arrays*, Integers 10, A14, 187–199. **A general theorem bounding multiplicities in integer arrays, best possible in general; recovers Singmaster's O(log t) for binomial coefficients and gives bounds for Narayana and Eulerian numbers.** (Formalization target: it generalizes our `LogBound.lean`.)
- **K. Matomäki, M. Radziwiłł, X. Shao, T. Tao, J. Teräväinen (2022)**, *Singmaster's conjecture in the interior of Pascal's triangle*, Q. J. Math. 73(3), 1137–1177; arXiv:2106.03335. Also treats falling factorials. Cited by only 4 papers on Semantic Scholar; none extends it toward the edges.
- **K. Matomäki, X. Shao, T. Tao, J. Teräväinen (2022)**, *Higher uniformity of arithmetic functions in short intervals I*, arXiv:2204.03754 (the analytic machinery behind the interior theorem).
- **Z. King, R. S. Williams (2026)**, *A bound for repeated binomial coefficients having large prime power factors*, NNTDM 32(2), 430–438. pᵠ ≥ t^{1/r} ⇒ N(t) ≤ 2r for large t.
- **F. Yudin (2026)**, *Square products of factorials and a conjecture of Erdős and Graham*, arXiv:2610.01899. Uses the MRSTT equidistribution estimate; not about multiplicities.
- Tangential users of AEH's normal-order result (I-convergence of arithmetic functions): Baláž–Gogola–Visnyai (JNT 2018), Tóth–Bukor–Filip (Period. Math. Hung. 2019), Baláž–Visnyai (2020).

## 4. The equation C(n, k) = C(m, l) for fixed (k, l)

Chronological; this is the "fixed (k, l)" strand that de Weger's Conjecture A packages.

- **L. J. Mordell (1963)**, *On the integer solutions of y(y+1) = x(x+1)(x+2)*, Pacific J. Math. 13, 1347–1351. Solutions (x, y) = (2, 1), (14, 5). de Weger 1997 notes this settles C(n, 3) = C(m, 4) "without anybody having realized it".
- **E. T. Avanesov (1966/67)**, *Solution of a problem on figurate numbers* (Russian), Acta Arith. 12, 409–420. C(n, 2) = C(m, 3): exactly the solutions giving 10, 120, 1540, 7140 (Sierpiński's problem).
- **P. Kiss (1988)**, *On the number of solutions of the Diophantine equation C(x, p) = C(y, 2)*, Fibonacci Quart. 26, 127–130. Finitely many solutions for each odd prime p (Baker's method). https://www.mathstat.dal.ca/FQ/Scanned/26-2/kiss.pdf
- **B. Brindza (1991)**, *On a special superelliptic equation*, Publ. Math. Debrecen 39, 159–162. C(x, n) = C(y, 2) has effectively finitely many solutions for every n ≥ 3.
- **S. P. Mohanty (1991)**, *Which triangular numbers are products of three consecutive integers?*, Acta Math. Hungar. 58, 31–36. x(x+1) = 2y(y+1)(y+2): six solutions.
- **Barja, Molinelli, Blanco Ferro (1993)** ⚠ — primality of the exponent in Kiss's theorem is unnecessary (cited by Gallegos-Ruiz et al.).
- **Á. Pintér (1995)**, *A note on the Diophantine equation C(x, 4) = C(y, 2)*, Publ. Math. Debrecen 47, 411–415.
- **B. M. M. de Weger (1996)**, *A binomial Diophantine equation*, Q. J. Math. 47, 221–231 (C(n, 2) = C(m, 4)).
- **B. M. M. de Weger (1997)**, *Equal binomial coefficients: some elementary considerations*, J. Number Theory 63, 373–386 (preprint 1995: https://repub.eur.nl/pub/1356). **Conjecture A** (see §1); search to 10^30 / rows ≤ 1000; C(n, 3) = C(m, 4) via Mordell; partial results on rational points of C(n, 3) = C(m, 4).
- **Á. Pintér, B. M. M. de Weger (1997)**, *210 = 14·15 = 5·6·7 = C(21, 2) = C(10, 4)*, Publ. Math. Debrecen 51, 175–189. Solves (y−1)y(y+1) = C(n, 4) and x(x+1) = C(n, 4) via Thue equations.
- **P. Goetgheluck (1998)**, *Infinite families of solutions of the equation C(n, k) = 2 C(a, b)*, Math. Comp. 67, 1727–1733. Collisions up to a factor 2 occur in infinite families (contrast with exact collisions).
- **R. J. Stroeker, B. M. M. de Weger (1999)**, *Elliptic binomial Diophantine equations*, Math. Comp. 68, 1257–1281. Complete solutions for (k, l) = (2,3), (2,4), (2,6), (2,8), (3,4), (3,6), (4,6), (4,8) via elliptic logarithms. 33 citing papers.
- **F. Beukers, T. N. Shorey, R. Tijdeman (1999)**, *Irreducibility of polynomials and arithmetic progressions with equal products of terms*, in Number Theory in Progress, 11–26. Ineffective finiteness for C(x, n) = a·C(y, m) type equations.
- **L. Hajdu, Á. Pintér (2000)**, *Combinatorial Diophantine equations*, Publ. Math. Debrecen 56, 391–403. Solves C(x, 6) = C(y, 2), C(x, 6) = C(y, 4), C(x, 3) = P_2(y), C(x, 3) = P_4(y), C(x, 6) = P_2(y), C(x, 6) = P_4(y) and sums-of-powers variants (SIMATH).
- **Yu. Bilu, R. Tichy (2000)**, *The Diophantine equation f(x) = g(y)*, Acta Arith. 95, 261–288. The general finiteness criterion behind most later "equal values" results.
- **A. Flammenkamp, F. Luca (2002)**, *Binomial coefficients and Lucas sequences*, J. Number Theory 93, 246–284. Binomial coefficients in Lucas sequences; finiteness for fixed k.
- **Cs. Rakaczki (2000)**, *Binomial coefficients in arithmetic progressions*, Publ. Math. Debrecen 56; **(2004)**, *On the Diophantine equation F(C(x, n)) = b C(y, m)*, Period. Math. Hungar. 49, 119–132 (generalizes BST).
- **F. Luca, L. Szalay (2004; 2006)**, linear and quadratic relations among consecutive binomial coefficients (Publ. Math. Debrecen 69).
- **Y. Bugeaud, M. Mignotte, S. Siksek, M. Stoll, Sz. Tengely (2008)**, *Integral points on hyperelliptic curves*, Algebra Number Theory 2, 859–885. Solves C(n, 5) = C(m, 2). **M. Stoll (2010)**, *How to solve a Diophantine equation*, arXiv:1002.4344 — expository account of this case.
- **T. Kovács (2011)**, *Combinatorial Diophantine equations*, PhD thesis, Debrecen (supervisor L. Hajdu). **Gy. Péter (2017)**, *Diophantine equations with separable variables*, thesis.
- **Yu. Bilu, C. Fuchs, F. Luca, Á. Pintér (2013)**, *Combinatorial Diophantine equations and a refinement of a theorem on separated variables equations*, Publ. Math. Debrecen 82, 219–254.
- **L. Hajdu, Á. Pintér, Sz. Tengely, N. Varga (2014)**, *Equal values of figurate numbers*, J. Number Theory 137, 130–141. Effective results; binomial coefficients, polygonal and pyramidal numbers as special cases. https://shrek.unideb.hu/~tengely/hptvrevised.pdf
- **K. Győry, T. Kovács, Gy. Péter (2014)**, *Equal values of standard counting polynomials*, Publ. Math. Debrecen 84, 259–277. Nine families of equations from equal lattice-point counts in cubes, simplices, pyramids, octahedra; survey + new results.
- **H. Jenkins (2014/2016)**, *Repeated binomial coefficients and high-degree curves*, Integers 16; arXiv:1411.4111. C(x, y) = C(x − a, y + b) finite for a ≠ b.
- **T. Kovács, Zs. Rábai (2018)**, *Equal values of pyramidal numbers*, Indag. Math. 29. **L. Hajdu, N. Varga (2020)**, *Polynomial values of figurate numbers*, J. Number Theory.
- **H. R. Gallegos-Ruiz, N. Katsipis, Sz. Tengely, M. Ulas (2019/2020)**, *On the Diophantine equation C(n, k) = C(m, l) + d*, J. Number Theory 209; arXiv:1904.11369. Solved for −3 ≤ d ≤ 3 and (k, l) = (2,3), (2,4), (2,5), (2,6), (2,8), (3,4), (3,6), (4,6), (4,8).
- **N. Katsipis (2019)**, *Diophantine equations coming from binomial near-collisions*, arXiv:1901.03841. Difference-1 near-collisions do not exist for (6,3), (3,6), (8,2).
- **T. Yamada (2020)**, *Necessary conditions for binomial collisions*, arXiv:2002.07043. Collisions near the centre require distant rows: l ≫ (n/log n)^{40/21}.
- **L. Hajdu, Á. Papp, R. Tijdeman (2022)**, *The Prouhet–Tarry–Escott problem, indecomposability of polynomials and Diophantine equations*, Ramanujan J. **L. Hajdu, R. Tijdeman (2023)**, *The Diophantine equation f(x) = g(y) for polynomials with simple rational roots*, J. London Math. Soc. 108. Characterizes when such equations have infinitely many solutions; equal products of consecutive integers.
- **M. Mihajlov Carević, M. Ilić, M. J. Petrović (2020)**, *Computing support for testing equal values of the figurative numbers in the Pascal triangle*, Technium 2(7) (computational; minor). **R. Rakamazi (2014; 2016)**, Teaching Math. Comput. Sci. (expository).

## 5. Computer searches
- **A. Blokhuis, A. Brouwer, B. de Weger (2017)**, *Binomial collisions and near collisions*, Integers 17, A64; arXiv:1707.06893. n ≤ 10^6 and values ≤ 10^60; near-collision families. (0 citing papers indexed on Semantic Scholar; cited by Katsipis.)
- Earlier search bounds: Singmaster 1975 (2^48), de Weger 1997 (10^30), D. W. Wilson (OEIS, 3.3·10^17), Ramirez 2026 (OEIS, 10^62) ⚠.

## 6. Central binomial coefficients (relevant to our C(2m, m) search)
- **P. Erdős, R. L. Graham, I. Z. Ruzsa, E. G. Straus (1975)**, *On the prime factors of C(2n, n)*, Math. Comp. 29, 83–92. https://www.ams.org/journals/mcom/1975-29-129/S0025-5718-1975-0369288-3/
- **A. Sárközy (1985)** (never squarefree for large n); **P. Goetgheluck (1988)**, **I. Vardi (1991)** (computational ranges); **J. W. Sander (1992)** (C(2n ± d, n)).
- **A. Granville, O. Ramaré (1996)**, *Explicit bounds on exponential sums and the scarcity of squarefree binomial coefficients*, Mathematika 43, 73–107. C(2n, n) squarefree only for n = 1, 2, 4.
- **T. Bang, B. Fuglede (1990)**, *No two quotients of normalized binomial mid-coefficients are equal*, J. Number Theory 35, 345–349. μ_q/μ_p = μ_s/μ_r has only trivial solutions, μ_n = 4^{-n} C(2n, n). **The only prior "equality" result about central coefficients found.**
- **S. Yang, A. Togbé, W. Wu (2013)**, *Diophantine equations involving normalized binomial mid-coefficients*, Publ. Math. Debrecen 83, 415–433 (power means of μ_n).
- **A. Straub, T. Amdeberhan, V. H. Moll (2008)**, *The p-adic valuation of k-central binomial coefficients*, arXiv:0811.2028.
- **S. T. Holdum, F. R. Klausen, P. M. R. Rasmussen**, *Powers in prime bases and a problem on central binomial coefficients*, Integers 15 (2015) A43; arXiv:2601.09510. Divisibility of C(2n, n) by 4 and 9.
- **E. Croot, H. Mousavi, M. Schmidt (2022)**, *On a conjecture of Graham on the p-divisibility of central binomial coefficients*, arXiv:2201.11274 (Graham's $1000 problem, gcd(C(2n, n), 105) = 1).
- **Kummer / Legendre in Mathlib** (v4.34): `Nat.factorization_choose`, `Nat.factorization_choose_eq_zero_of_lt` (n < p ⇒ v_p = 0), `Nat.factorization_choose_le_one` (n < p² ⇒ v_p ≤ 1), `Nat.factorization_choose_of_lt_three_mul`, `Nat.factorization_centralBinom_*` in `Mathlib/Data/Nat/Choose/Factorization.lean`; `Nat.emultiplicity_choose` in `Mathlib/Data/Nat/Multiplicity.lean`. These suffice to formalize the valuation filter in `singsearch.py` (window (n−k, n] contains a multiple of p iff p | C(n, k), for p > k).

## 7. Perfect powers and products (neighbouring strand)
- **P. Erdős (1951)**, *On a Diophantine equation*, J. London Math. Soc. 26, 176–178 ⚠: C(n, k) ≠ x^l for k ≥ 4. **K. Győry (1997)**, *On the Diophantine equation C(n, k) = x^l*, Acta Arith. 80, 289–295: completes k = 2, 3 (uses Darmon–Merel 1997). **Erdős–Selfridge (1975)** on products of consecutive integers.
- **H. W. Gould (1971)**, *Equal products of generalized binomial coefficients*, Fibonacci Quart. 9; **C. T. Long, V. E. Hoggatt (1974)**, *Sets of binomial coefficients with equal products*, Fibonacci Quart. 12. The "hexagon" product identities (coincidences of products, not values).

## 8. Generalizations and structural explanations
- **J.-M. de Koninck, N. Doyon, W. Verreault (2021)**, multinomial coefficients, Integers 21, A34; arXiv:2107.09107.
- **A. Bazsó, I. Mező, Á. Pintér, Sz. Tengely (2023)**, Stirling numbers, arXiv:2311.06080 (Int. J. Number Theory).
- **T. Richmond, M. Sword (2023)**, *An arithmetic triangle arising from a one-way street grid*, College Math. J. (cites AEH; multiplicities in another triangle).
- **E. Lupercio, E. Shaydurova (2026)**, *Seven coincidences and sixty symmetries*, arXiv:2610.00572. A₅-representation explanations of the coincidences at 1540, 7140, 3003 (answering a question of J. Baez).
- **W. Q. Erickson, M. Hunziker (2023)**, *Dimension identities, almost self-conjugate partitions, and BGG complexes*, arXiv:2301.09744. Cites de Weger 1997; infinite families of dimension identities between gl_n and gl_{n+m} modules (possible structural source of binomial coincidences — unverified from abstract).
- **V. Dotsenko, M. Jumadildayev (2026)**, arXiv:2609.33480; **F. N. Castro, O. E. González, L. A. Medina (2017)**, IEEE Trans. Inf. Theory — both only superficially related (binomial coefficients as dimensions / linear Diophantine equations).

## 9. Formalization status
- **google-deepmind/formal-conjectures**, `FormalConjectures/Wikipedia/Singmaster.lean`: statement only.
- No Lean/Isabelle/Coq formalization of Singmaster's bound, N(3003) = 8, the Lind identity, or Clark's theorem found. Mizar has Pascal's triangle and Lucas's theorem (R. Ziobro, Formalized Math. 2024).

## 10. Gaps to close before writing a paper
1. Read de Weger 1997 (JNT) §1–2 and BBdW 2017 §2 for any remark on central coefficients or on Lind members beyond i = 2.
2. Read Clark 2010 in full: if his general theorem is sharp for binomial arrays, `LogBound.lean` could be upgraded to it.
3. Locate the Ramirez 2026 search (OEIS A003015) and Montanus–Westdijk p. 69.
4. Check Erickson–Hunziker 2023 §? for whether dimension identities produce C(n, k) = C(m, l) coincidences beyond the known ones.
5. MathSciNet/zbMATH search: "central binomial coefficient" AND "equal binomial coefficients".
6. Verify the ⚠ items.

## 11. Full-text checks (2026-10-25)

Read in full (PDF text) and searched for central coefficients, odd multiplicities and checks of
Lind members: Blokhuis–Brouwer–de Weger 2017, de Weger 1995/97, Yamada 2020, Jenkins 2014,
MRSTT 2022, de Koninck–Doyon–Verreault 2021, Bazsó–Mező–Pintér–Tengely 2023, King–Williams 2026,
Katsipis 2019, Gallegos-Ruiz–Katsipis–Tengely–Ulas 2019, Kane 2004 and 2007, Clark 2010.

- **Blokhuis–Brouwer–de Weger, Theorem 2.2** (exact statement): no unknown collisions for
  (k, l) ∈ {(2,3), (2,4), (2,5), (2,6), (2,8), (3,4), (3,6), (4,6), (4,8)}; for adjacent rows
  (m, l) = (n − 1, k + 1), (n − 1, k + 2), (n − 2, k + 1); for n ≤ 10^6; and for C(n, k) ≤ 10^60.
  Their Conjecture 2.1 is de Weger's Conjecture A. They list the Lind members up to
  C(4895, 1869) but make no statement about their multiplicity beyond these searches.
  **Consequence for us:** their n ≤ 10^6 search already excludes a third representation of the Lind
  members i = 3–6 in rows ≤ 10^6; our search adds all larger rows (and i = 7, 8, 9 have rows
  1.58·10^6, 1.08·10^7, 7.4·10^7, outside their range entirely).
- **Yamada 2020, Theorem 1.1** covers central coefficients: in his equation
  C(2n + δ, n − m) = C(2n + l, n − k) (δ ∈ {0, 1}, 0 ≤ m < k < n/2, m ≤ 0.735k), the case
  m = δ = 0 is C(2n, n) = C(2n + l, n − k), and he proves l > n(1.3132 log₂(2n) − 2.00271) (and
  l > (cn/log n)^{40/21} for c < 0.68943 and large n). So a second representation of a central
  coefficient must lie in a row far beyond 2n. **This is the closest prior work on central
  collisions** — a lower bound on the other row, not an exclusion; our computation complements it.
  His proof also uses prime gaps (d(p) ≤ 456 for p ≤ 3.2·10^10) and a search over 572,960 primes,
  close in spirit to our prime-in-window filter.
- **Kane 2004, 2007**: no computations and nothing on central coefficients; Kane 2007 remarks
  that "essentially no other lower bounds on N(t) are known" beyond N(3003) = 8 and the family.
- **Clark 2010**, Theorem 2: for a "normal array" (semi-triangular, increasing, semi-unimodal,
  multiplicity r per row, Δ-bounded peak, growth function g), N_a(t) < r(g⁻¹(t) + Δ). For Pascal's
  triangle (r = 2, Δ = 1, g(x) = 2^x) this is N(t) < 2(log₂ t + 1); our `LogBound.lean`
  (N(t) ≤ 2⌊log₂ t⌋) is slightly sharper. Formalizing Clark's general theorem would also cover
  Narayana and Eulerian numbers.
- Nothing in these papers searches central binomial coefficients for collisions, and nothing
  checks Lind members beyond listing them. The novelty assessment in §1 stands, with the BBdW
  rows ≤ 10^6 caveat for i = 3–6 and Yamada as the theoretical context for the central search.

## 12. Unverified 2026 claims (checked 2026-10-25)

- J. Reed, *Bounding Singmaster's Conjecture via Constructive Type Transformation in Lean 4*,
  Zenodo 10.5281/zenodo.21660302 (2026-07-29), code at github.com/AEjonanonymous/Singmasters-Conjecture.
  The abstract claims a complete formally verified resolution while also saying the general case
  remains open; the Lean file is 5 kB. Not checked further; not a peer-reviewed result.
- CreizyLabs / J. Emerick, prize claim TheJustinSunPrize/awards PR #4709 (opened 2026-10-05):
  claims a kernel-verified Lean proof of a bound N(a) ≤ M. Closed by the reviewer on 2026-10-22
  as not a complete solution.
- Neither covers exact multiplicities of specific numbers or the central case, so they do not
  affect the novelty of `Collisions.lean` / `Central.lean` or of the searches.
