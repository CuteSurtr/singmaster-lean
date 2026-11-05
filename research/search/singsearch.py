#!/usr/bin/env python3
"""Search for representations t = C(n, k), 2 <= k, of structured numbers t.

For a fixed k, a solution n of C(n, k) = t lies in the bracket [x, x + k - 1], where
x = floor((k! t)^(1/k)), because (n - k + 1)^k <= k! t <= n^k. Candidates in the bracket are
discarded with necessary conditions from p-adic valuations: for a prime p > k,
v_p(C(n, k)) is the number of multiples of p in the window (n - k, n] (counted with
multiplicity), and the window contains at most one multiple because it is shorter than p. So
if v_p(t) = 0 the window contains no multiple of p, and if v_p(t) >= 1 it contains one. The
candidates that survive every prime are checked exactly with C(n, k) == t.

Modes:
  selftest  compare the filtered search with an unfiltered exact search
  central   t = C(2m, m), k in [2, m - 1]   (an odd multiplicity N(t) >= 5 needs a hit here)
  lind      t = C(F(2i+2) F(2i+3), F(2i) F(2i+3)), all k with C(2k, k) <= t
  merge     combine JSON results and report the contiguous range that was covered
"""
import argparse
import bisect
import json
import math
import os
import sys
import time
from multiprocessing import Pool

try:
    import gmpy2

    mpz = gmpy2.mpz
    comb = gmpy2.comb
    fac = gmpy2.fac

    def iroot(a, k):
        return gmpy2.iroot(a, k)[0]
except ImportError:  # slow fallback, for small local tests only
    mpz = int
    comb = math.comb
    fac = math.factorial

    def iroot(a, k):
        if a < 2:
            return a
        x = 1 << ((a.bit_length() + k - 1) // k)
        while True:
            y = ((k - 1) * x + a // x ** (k - 1)) // k
            if y >= x:
                return x
            x = y


try:
    import mpmath
except ImportError:
    mpmath = None

HAVE_MPFR = "gmpy2" in globals() and hasattr(gmpy2, "lngamma")
LN10 = math.log(10)


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, math.isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i :: i] = bytearray(len(range(i * i, n + 1, i)))
    return [i for i in range(n + 1) if sieve[i]]


def carries(a, b, p):
    """Kummer: v_p(C(a + b, a)) is the number of carries when adding a and b in base p."""
    c = carry = 0
    while a or b or carry:
        carry = 1 if a % p + b % p + carry >= p else 0
        c += carry
        a //= p
        b //= p
    return c


def restrict(J, L, k, p, s, contains):
    """Intersect the candidate offsets J (disjoint sorted inclusive intervals in [0, L - 1])
    with the offsets j for which the window (A + j - k, A + j] contains a multiple of p (or,
    if not contains, does not). Here s = (-A) mod p and p > k, so the windows that contain a
    multiple are exactly j in [s + q p, s + q p + k - 1] for integers q."""
    A = []
    q = -1
    while s + q * p <= L - 1:
        lo, hi = max(0, s + q * p), min(L - 1, s + q * p + k - 1)
        if lo <= hi:
            A.append((lo, hi))
        q += 1
    if not contains:
        comp, cur = [], 0
        for lo, h in A:
            if lo > cur:
                comp.append((cur, lo - 1))
            cur = max(cur, h + 1)
        if cur <= L - 1:
            comp.append((cur, L - 1))
        A = comp
    out = []
    for lo, h in J:
        for a, b in A:
            l2, h2 = max(lo, a), min(h, b)
            if l2 <= h2:
                out.append((l2, h2))
    return out


# Miller-Rabin with the first 13 prime bases is deterministic below psi_13
# (Sorenson and Webster, Math. Comp. 86 (2017), 985-1003).
MR_BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41)
MR_LIMIT = 3317044064679887385961981


def is_prime_det(x):
    """Primality for 0 <= x < MR_LIMIT, proven correct in that range."""
    x = int(x)
    assert x < MR_LIMIT
    if x < 2:
        return False
    for p in MR_BASES:
        if x % p == 0:
            return x == p
    d, s = x - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in MR_BASES:
        y = pow(a, d, x)
        if y == 1 or y == x - 1:
            continue
        for _ in range(s - 1):
            y = y * y % x
            if y == x - 1:
                break
        else:
            return False
    return True


def window_filter(J, A, k, p0, B):
    """Remove the offsets j whose window (A + j - k, A + j] contains a killer: a prime P > k
    that does not divide t. Killers up to B come from p0 (sieved primes with v_P(t) = 0);
    every prime above B is a killer (all prime factors of t are at most B) and is found with
    is_prime_det, which needs A + j < MR_LIMIT; above that only p0 is used.
    A killer P does not divide k!, so it would divide C(n, k). Returns (J', primality tests)."""
    out, tests = [], 0
    floor_k = k  # killers must exceed k

    def last_killer(n):
        """Largest killer in (max(n - k, k), n], or None."""
        nonlocal tests
        lo = max(n - k, floor_k)
        best = None
        if n > B and n < MR_LIMIT:
            x, stop = n, max(lo, B)
            while x > stop:
                tests += 1
                if is_prime_det(x):
                    return x
                x -= 1
        i = bisect.bisect_right(p0, min(n, B)) - 1
        if i >= 0 and p0[i] > lo:
            best = p0[i]
        return best

    def next_killer(n, limit):
        """Smallest killer in (n, limit], or None."""
        nonlocal tests
        cand = None
        i = bisect.bisect_right(p0, n)
        if i < len(p0) and p0[i] <= limit:
            cand = p0[i]
        top = limit if cand is None else cand - 1
        x = max(n, B) + 1
        if x <= top and top < MR_LIMIT:
            while x <= top:
                tests += 1
                if is_prime_det(x):
                    return x
                x += 1
        elif x <= top:
            return cand  # cannot test primes this large; fall back to sieved killers only
        return cand

    for lo, hi in J:
        n, nhi = A + lo, A + hi
        while n <= nhi:
            P = last_killer(n)
            if P is not None:
                n = P + k  # P lies in the window of every n' in [P, P + k - 1]
                continue
            Q = next_killer(n, nhi)
            if Q is None:
                out.append((n - A, nhi - A))
                break
            out.append((n - A, Q - 1 - A))
            n = Q
    return out, tests


def bracket(t, k, logt, dps):
    """An interval [A, A + L - 1] containing every n with C(n, k) = t.
    Exactly: (n - k + 1)^k <= k! t <= n^k, so n lies in [ceil(r), floor(r) + k - 1] for
    r = (k! t)^(1/k). If r is below 10^(dps - 20), r is computed in floating point and widened
    by a relative 10^-(dps - 15): with gmpy2 (MPFR, correctly rounded log, lngamma and exp,
    precision 4 dps bits) or mpmath at dps digits. Otherwise x = floor(r) is computed exactly.
    logt must be log(t) at that precision (see log_of)."""
    if logt is not None:
        if HAVE_MPFR:
            ctx = gmpy2.get_context()
            old = ctx.precision
            ctx.precision = 4 * dps
            try:
                lr = (gmpy2.lngamma(gmpy2.mpfr(k + 1)) + logt) / k
                if lr < (dps - 20) * LN10:
                    r = gmpy2.exp(lr)
                    eps = gmpy2.mpfr(10) ** (-(dps - 15))
                    lo = int(gmpy2.ceil(r * (1 - eps)))
                    hi = int(gmpy2.floor(r * (1 + eps))) + k - 1
                    return mpz(lo), hi - lo + 1
            finally:
                ctx.precision = old
        else:
            with mpmath.workdps(dps):
                lr = (mpmath.loggamma(k + 1) + logt) / k
                if lr < (dps - 20) * mpmath.log(10):
                    r = mpmath.exp(lr)
                    eps = mpmath.mpf(10) ** (-(dps - 15))
                    lo = int(mpmath.ceil(r * (1 - eps)))
                    hi = int(mpmath.floor(r * (1 + eps))) + k - 1
                    return mpz(lo), hi - lo + 1
    return iroot(fac(k) * t, k), k


_SPLIT_CACHE = {}


def split_primes(plist, elist):
    """(primes with v_p(t) = 0 ascending, primes with v_p(t) >= 1 descending, the same
    ascending), cached per list."""
    key = id(plist)
    hit = _SPLIT_CACHE.get(key)
    if hit is not None and hit[0] is plist:
        return hit[1], hit[2], hit[3]
    p0 = [p for p, e in zip(plist, elist) if e == 0]
    p1_asc = [p for p, e in zip(plist, elist) if e >= 1]
    p1 = p1_asc[::-1]
    _SPLIT_CACHE.clear()
    _SPLIT_CACHE[key] = (plist, p0, p1, p1_asc)
    return p0, p1, p1_asc


def gap_kill(J, A, k, p1_asc):
    """Drop every interval of candidates n whose windows (n - k, n] all miss the multiples of
    some prime p > k that divides t. That happens when p > max(n_hi, k) (no multiple up to
    n_hi), or when max(k, n_hi / 2) < p <= n_lo - k (p lies below every window and 2p above).
    Typical use: for k between N / (2 phi) and K, the candidates just above N survive the other
    filters, and the primes dividing C(N, K) just below N - k remove them."""
    if not p1_asc:
        return J
    top = p1_asc[-1]
    out = []
    for lo, hi in J:
        n_lo, n_hi = A + lo, A + hi
        if top > max(n_hi, k):
            continue
        i = bisect.bisect_right(p1_asc, max(k, n_hi // 2))
        if i < len(p1_asc) and p1_asc[i] <= n_lo - k:
            continue
        out.append((lo, hi))
    return out


def solve_k(t, k, plist, elist, logt=None, dps=60, max_primes=400, max_exact=64,
            B=None, nmin=None, nmax=None, pw_after=12):
    """All n with C(n, k) = t (and n >= nmin, if given). plist/elist: ascending primes p with
    v_p(t). B: every prime factor of t is at most B (enables the prime-in-window filter).
    Returns (solutions, valuation primes used, primality tests, exact checks)."""
    A, L = bracket(t, k, logt, dps)
    J = [(0, L - 1)]
    lo_j = int(max(0, nmin - A)) if nmin is not None else 0
    hi_j = int(min(L - 1, nmax - A)) if nmax is not None else int(L - 1)
    J = [(lo_j, hi_j)] if lo_j <= hi_j else []
    # The most selective primes p > k: those dividing t, largest first (a window of length k
    # contains a multiple of p for about a fraction k/p of the candidates), and those not
    # dividing t, smallest first (a window avoids every multiple for about 1 - k/p of them).
    p0, p1, p1_asc = split_primes(plist, elist)
    i0 = bisect.bisect_right(p0, k)
    i1 = 0
    used = tests = 0
    take_p1 = True
    pw_done = False
    while J and used < max_primes:
        if not pw_done and used >= pw_after and B is not None:
            J, tests = window_filter(J, A, k, p0, B)
            J = gap_kill(J, A, k, p1_asc)
            pw_done = True
            continue
        have1 = i1 < len(p1) and p1[i1] > k
        have0 = i0 < len(p0)
        if not (have0 or have1):
            break
        if (take_p1 and have1) or not have0:
            p, contains = p1[i1], True
            i1 += 1
        else:
            p, contains = p0[i0], False
            i0 += 1
        take_p1 = not take_p1
        J = restrict(J, L, k, p, int((-A) % p), contains)
        used += 1
    if J and not pw_done and B is not None:
        J, tests = window_filter(J, A, k, p0, B)
    J = gap_kill(J, A, k, p1_asc)
    if not J:
        return [], used, tests, 0
    count = int(sum(h - l + 1 for l, h in J))
    sols = []
    if count <= max_exact:
        for lo, h in J:
            for j in range(lo, h + 1):
                n = A + j
                if comb(n, k) == t:
                    sols.append(int(n))
        return sols, used, tests, count
    # Too many survivors: binary search the bracket exactly (C(n, k) increases in n).
    lo, hi = A, A + L - 1
    checks = 0
    while lo < hi:
        mid = (lo + hi) // 2
        checks += 1
        if comb(mid, k) < t:
            lo = mid + 1
        else:
            hi = mid
    checks += 1
    if comb(lo, k) == t and (nmin is None or lo >= nmin) and (nmax is None or lo <= nmax):
        sols.append(int(lo))
    return sols, used, tests, checks


def log_of(t, dps):
    """log(t) for bracket(): an MPFR number at 4 dps bits, or an mpmath number at dps digits."""
    if HAVE_MPFR:
        ctx = gmpy2.get_context()
        old = ctx.precision
        ctx.precision = 4 * dps
        try:
            return gmpy2.log(gmpy2.mpfr(t))
        finally:
            ctx.precision = old
    if mpmath is None:
        return None
    with mpmath.workdps(dps):
        return mpmath.log(mpmath.mpf(int(t)))


def brute_k(t, k):
    """Unfiltered exact search over the same bracket (used by the self-test)."""
    x = iroot(fac(k) * t, k)
    return [int(x + j) for j in range(k) if comb(x + j, k) == t]


def generic_vals(t, bound):
    ps = primes_upto(bound)
    es = []
    for p in ps:
        e, u = 0, t
        while u % p == 0:
            u //= p
            e += 1
        es.append(e)
    return ps, es


def largest_factor(t, ps, es):
    """Largest prime factor of t if t factors completely over the primes ps, else None."""
    u, big = t, None
    for p, e in zip(ps, es):
        if e:
            u //= p ** e
            big = p
    return big if u == 1 else None


def kmax_for(t):
    """Largest k with C(2k, k) <= t (a solution with k <= n/2 has C(2k, k) <= C(n, k))."""
    k = 1
    while comb(2 * (k + 1), k + 1) <= t:
        k += 1
    return k


def kmax_bound(t):
    """An upper bound for kmax_for(t): C(2k, k) >= 4^k / (2 sqrt(k)), so C(2k, k) <= t gives
    2k <= log2(t) + 1 + log2(k)/2 < bitlength(t) + 21 for k < 2^40."""
    return (t.bit_length() + 21) // 2


# ----------------------------------------------------------------------------- central


def central_one(m, dps=60, use_log=True):
    t = comb(2 * m, m)
    plist = primes_upto(2 * m)
    elist = [carries(m, m, p) for p in plist]
    logt = log_of(t, dps) if use_log else None
    sols, used, exact, tests = [], 0, 0, 0
    for k in range(2, m):
        # Any solution has n > 2m: for n <= 2m and k < m, C(n, k) <= C(2m, k) < C(2m, m).
        # Every prime factor of C(2m, m) is at most 2m.
        s, u, pt, c = solve_k(t, k, plist, elist, logt, dps, B=2 * m, nmin=2 * m + 1)
        used += u
        tests += pt
        exact += c
        sols += [[n, k] for n in s]
    return {"m": m, "solutions": sols, "primes_used": used, "prime_tests": tests,
            "exact_checks": exact}


def run_central(args):
    deadline = time.time() + args.minutes * 60
    stride = args.jobs * args.workers
    if args.mlist:
        # An explicit ascending list of m, shared out round-robin so that all lanes advance
        # through it together.
        values = sorted(set(json.load(open(args.mlist))))
        tasks = [(w, values[args.job * args.workers + w::stride]) for w in range(args.workers)]
    else:
        tasks = [(w, list(range(args.start + args.job * args.workers + w, args.stop, stride)))
                 for w in range(args.workers)]
    with Pool(args.workers) as pool:
        parts = pool.starmap(central_worker, [(ms, deadline, args.dps) for _, ms in tasks])
    out = {"mode": "central", "job": args.job, "jobs": args.jobs, "workers": args.workers,
           "start": args.start, "stop": args.stop, "mlist": args.mlist, "lanes": parts}
    json.dump(out, open(args.out, "w"))
    done = sum(len(p["results"]) for p in parts)
    hits = [r for p in parts for r in p["results"] if r["solutions"]]
    print(f"central job {args.job}: {done} values of m done, hits: {hits}")


def central_worker(ms, deadline, dps):
    res, t0 = [], time.time()
    for m in ms:
        if time.time() > deadline:
            break
        r = central_one(m, dps)
        res.append(r)
    return {"assigned": ms, "results": res, "seconds": time.time() - t0}


# ----------------------------------------------------------------------------- lind


def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def lind_member(i):
    return fib(2 * i + 2) * fib(2 * i + 3), fib(2 * i) * fib(2 * i + 3)


def lind_worker(i, start, stride, kmax, deadline, dps):
    """Search k = start, start + stride, ... <= kmax in order, until the deadline.
    Records totals, every hit, and every k that needed exact checks or hit the prime cap."""
    N, K = lind_member(i)
    t = comb(N, K)
    plist = primes_upto(N)
    elist = [carries(K, N - K, p) for p in plist]
    logt = log_of(t, dps)
    t0 = time.time()
    done = 0
    hits, heavy = [], []
    tot = {"primes": 0, "tests": 0, "exact": 0}
    for k in range(start, kmax + 1, stride):
        if time.time() > deadline:
            break
        # For k < K a solution has n > N: C(n, k) <= C(N, k) < C(N, K) when n <= N.
        # For K + 1 < k <= kmax a solution has n <= N - 2: C(N - 1, k) > C(N - 1, K + 1) = t.
        # Every prime factor of C(N, K) is at most N.
        s, u, pt, c = solve_k(t, k, plist, elist, logt, dps, B=N,
                              nmin=N + 1 if k < K else None,
                              nmax=N - 2 if k > K + 1 else None)
        done += 1
        tot["primes"] += u
        tot["tests"] += pt
        tot["exact"] += c
        if s:
            hits.append([k, s])
        if c or u >= 400:
            heavy.append([k, u, pt, c])
    assigned = len(range(start, kmax + 1, stride))
    return {"i": i, "start": start, "stride": stride, "assigned": assigned, "done": done,
            "hits": hits, "heavy": heavy, "totals": tot, "seconds": time.time() - t0}


def run_lind(args):
    deadline = time.time() + args.minutes * 60
    N, K = lind_member(args.i)
    t = comb(N, K)
    kmax = kmax_bound(t) if args.kmax is None else args.kmax
    # nmax = N - 2 for k > K + 1 needs C(N - 1, k) > C(N - 1, K + 1), i.e. k < N - 2 - K.
    assert kmax < N - 2 - K, (kmax, N - 2 - K)
    stride = args.jobs * args.workers
    starts = [args.kstart + args.job * args.workers + w for w in range(args.workers)]
    with Pool(args.workers) as pool:
        parts = pool.starmap(lind_worker, [(args.i, st, stride, kmax, deadline, args.dps)
                                           for st in starts])
    out = {"mode": "lind", "i": args.i, "N": N, "K": K, "digits": len(str(t)), "kmax": kmax,
           "kstart": args.kstart, "job": args.job, "jobs": args.jobs, "workers": args.workers,
           "lanes": parts}
    json.dump(out, open(args.out, "w"))
    found = [h for p in parts for h in p["hits"]]
    print(f"lind i={args.i} job {args.job}: kmax={kmax}, hits (k, n): {found}, "
          f"done {sum(p['done'] for p in parts)} of {sum(p['assigned'] for p in parts)}")


# ----------------------------------------------------------------------------- merge


def run_merge(args):
    central, lind = {}, {}
    for path in args.files:
        d = json.load(open(path))
        if d["mode"] == "central":
            for lane in d["lanes"]:
                for r in lane["results"]:
                    central[r["m"]] = r
            continue
        e = lind.setdefault(d["i"], {"N": d["N"], "K": d["K"], "digits": d["digits"],
                                      "kmax": d["kmax"], "lanes": {}, "hits": []})
        for lane in d["lanes"]:
            if "start" in lane:  # compact format
                e["lanes"][lane["start"]] = lane
                e["hits"] += lane["hits"]
                e["stride"] = lane["stride"]
            else:  # older per-k format
                for r in lane["results"]:
                    if r[1]:
                        e["hits"].append([r[0], r[1]])
    report = {}
    if central:
        m = min(central)
        while m + 1 in central:
            m += 1
        hits = {mm: r["solutions"] for mm, r in central.items() if r["solutions"]}
        report["central"] = {"contiguous_from": min(central), "contiguous_to": m,
                             "values_done": len(central), "hits": hits,
                             "exact_checks": sum(r["exact_checks"] for r in central.values()),
                             "prime_tests": sum(r.get("prime_tests", 0) for r in central.values()),
                             "primes_used": sum(r["primes_used"] for r in central.values())}
    for i, e in sorted(lind.items()):
        lanes = e["lanes"]
        stride = e.get("stride")
        cover = None
        if lanes and stride and len(lanes) == stride:
            # every residue class 2 + r (mod stride) has its own lane
            bounds = []
            for st, ln in lanes.items():
                if ln["done"] >= ln["assigned"]:
                    bounds.append(e["kmax"])
                else:
                    bounds.append(st + ln["done"] * stride - 1)
            cover = min(bounds)
        report[f"lind_{i}"] = {"N": e["N"], "K": e["K"], "digits": e["digits"],
                               "kmax": e["kmax"], "k_from": min(lanes) if lanes else None,
                               "k_contiguous_to": cover,
                               "complete": cover is not None and cover >= e["kmax"],
                               "hits": sorted(e["hits"]),
                               "lanes_seen": len(lanes), "stride": stride}
    json.dump(report, open(args.out, "w"), indent=1, sort_keys=True)
    print(json.dumps(report, indent=1, sort_keys=True))


# ----------------------------------------------------------------------------- selftest


def run_selftest(args):
    # 1. Known collisions, with valuations from trial division.
    known = {120: [(16, 2), (10, 3)], 210: [(21, 2), (10, 4)], 1540: [(56, 2), (22, 3)],
             3003: [(78, 2), (15, 5), (14, 6)], 7140: [(120, 2), (36, 3)],
             11628: [(153, 2), (19, 5)], 24310: [(221, 2), (17, 8)],
             61218182743304701891431482520: [(104, 39), (103, 40)]}
    for t, expect in known.items():
        t = mpz(t)
        ps, es = generic_vals(t, 4000)
        B = largest_factor(t, ps, es)
        got = []
        for k in range(2, kmax_for(t) + 1):
            s = solve_k(t, k, ps, es, log_of(t, 60))[0]
            assert s == brute_k(t, k), (t, k)
            assert solve_k(t, k, ps, es)[0] == s, (t, k)
            assert solve_k(t, k, ps, es, log_of(t, 60), B=B)[0] == s, (t, k)
            got += [(n, k) for n in s if 2 * k <= n]
        assert sorted(got) == sorted(expect), (int(t), got, expect)
    print("known collisions recovered")
    # 2. Random binomial coefficients: filtered search equals unfiltered search.
    import random
    rng = random.Random(1)
    for _ in range(args.random):
        n = rng.randrange(6, 140)
        kk = rng.randrange(2, n // 2 + 1)
        t = mpz(comb(n, kk))
        ps, es = generic_vals(t, 2 * n + 10)
        for k in range(2, kmax_for(t) + 1):
            b = brute_k(t, k)
            assert solve_k(t, k, ps, es)[0] == b, (n, kk, k)
            assert solve_k(t, k, ps, es, log_of(t, 30), 30)[0] == b, (n, kk, k)
            assert solve_k(t, k, ps, es, log_of(t, 30), 30, B=n, pw_after=0)[0] == b, (n, kk, k)
    print(f"{args.random} random binomial coefficients agree with the unfiltered search")
    # 3. Central coefficients: Kummer valuations and the unfiltered search agree.
    for m in range(2, args.central + 1):
        t = comb(2 * m, m)
        plist = primes_upto(2 * m)
        elist = [carries(m, m, p) for p in plist]
        for k in range(2, m):
            s = solve_k(t, k, plist, elist, log_of(t, 60), B=2 * m, nmin=2 * m + 1, pw_after=0)[0]
            assert s == [n for n in brute_k(t, k) if n > 2 * m], (m, k)
        r = central_one(m)
        assert central_one(m, use_log=False)["solutions"] == r["solutions"]
        t = comb(2 * m, m)
        for k in range(2, m):
            assert brute_k(t, k) == [], (m, k)
        assert r["solutions"] == [], r
    print(f"central m <= {args.central}: no other representations; filter agrees")
    # 4. Lind members recover their two known representations.
    for i in range(1, args.lind + 1):
        N, K = lind_member(i)
        t = comb(N, K)
        plist = primes_upto(N)
        elist = [carries(K, N - K, p) for p in plist]
        got = []
        for k in range(2, kmax_for(t) + 1):
            s = solve_k(t, k, plist, elist, log_of(t, 60), B=N, nmin=N + 1 if k < K else None,
                        nmax=N - 2 if k > K + 1 else None)[0]
            got += [(n, k) for n in s if 2 * k <= n]
        print(f"lind i={i}: C({N},{K}) has representations {sorted(got)}")
        assert (N, K) in got and (N - 1, K + 1) in got
    print("selftest passed")


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="mode", required=True)
    s = sub.add_parser("selftest")
    s.add_argument("--random", type=int, default=200)
    s.add_argument("--central", type=int, default=60)
    s.add_argument("--lind", type=int, default=2)
    c = sub.add_parser("central")
    for a in ("--job", "--jobs", "--workers"):
        c.add_argument(a, type=int, required=True)
    c.add_argument("--start", type=int)
    c.add_argument("--stop", type=int)
    c.add_argument("--mlist", help="JSON list of m to search instead of --start/--stop")
    c.add_argument("--minutes", type=float, default=60)
    c.add_argument("--dps", type=int, default=60)
    c.add_argument("--out", required=True)
    l = sub.add_parser("lind")
    for a in ("--i", "--job", "--jobs", "--workers"):
        l.add_argument(a, type=int, required=True)
    l.add_argument("--kmax", type=int)
    l.add_argument("--kstart", type=int, default=2, help="first k to search (default 2)")
    l.add_argument("--minutes", type=float, default=60)
    l.add_argument("--dps", type=int, default=60)
    l.add_argument("--out", required=True)
    g = sub.add_parser("merge")
    g.add_argument("files", nargs="+")
    g.add_argument("--out", required=True)
    args = ap.parse_args()
    if args.mode == "central" and not args.mlist and (args.start is None or args.stop is None):
        ap.error("central needs --mlist or both --start and --stop")
    {"selftest": run_selftest, "central": run_central, "lind": run_lind,
     "merge": run_merge}[args.mode](args)


if __name__ == "__main__":
    main()
