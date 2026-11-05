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


def bracket(t, k, logt, dps):
    """An interval [A, A + L - 1] containing every n with C(n, k) = t.
    Exactly: (n - k + 1)^k <= k! t <= n^k, so n lies in [ceil(r), floor(r) + k - 1] for
    r = (k! t)^(1/k). If r is below 10^(dps - 20), r is computed with mpmath at dps digits and
    widened by a relative 10^-(dps - 15); otherwise x = floor(r) is computed exactly."""
    if logt is not None:
        with mpmath.workdps(dps):
            lr = (mpmath.loggamma(k + 1) + logt) / k
            if lr < (dps - 20) * mpmath.log(10):
                r = mpmath.exp(lr)
                eps = mpmath.mpf(10) ** (-(dps - 15))
                lo = int(mpmath.ceil(r * (1 - eps)))
                hi = int(mpmath.floor(r * (1 + eps))) + k - 1
                return mpz(lo), hi - lo + 1
    return iroot(fac(k) * t, k), k


def solve_k(t, k, plist, elist, logt=None, dps=60, max_primes=400, max_exact=64):
    """All n with C(n, k) = t. plist/elist: ascending primes p with v_p(t).
    Returns (solutions, primes_used, exact_checks)."""
    A, L = bracket(t, k, logt, dps)
    J = [(0, L - 1)]
    i_lo = bisect.bisect_right(plist, k)
    i_hi = len(plist) - 1
    used = 0
    take_top = True
    while J and i_lo <= i_hi and used < max_primes:
        if take_top:
            idx, i_hi = i_hi, i_hi - 1
        else:
            idx, i_lo = i_lo, i_lo + 1
        take_top = not take_top
        p = plist[idx]
        J = restrict(J, L, k, p, int((-A) % p), elist[idx] >= 1)
        used += 1
    if not J:
        return [], used, 0
    count = sum(h - l + 1 for l, h in J)
    sols = []
    if count <= max_exact:
        for lo, h in J:
            for j in range(lo, h + 1):
                n = A + j
                if comb(n, k) == t:
                    sols.append(int(n))
        return sols, used, count
    # Too many survivors: binary search the whole bracket exactly (C(n, k) increases in n).
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
    if comb(lo, k) == t:
        sols.append(int(lo))
    return sols, used, checks


def log_of(t, dps):
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
    sols, used, exact = [], 0, 0
    for k in range(2, m):
        s, u, c = solve_k(t, k, plist, elist, logt, dps)
        used += u
        exact += c
        sols += [[n, k] for n in s]
    return {"m": m, "solutions": sols, "primes_used": used, "exact_checks": exact}


def run_central(args):
    deadline = time.time() + args.minutes * 60
    stride = args.jobs * args.workers
    tasks = [(w, list(range(args.start + args.job * args.workers + w, args.stop, stride)))
             for w in range(args.workers)]
    with Pool(args.workers) as pool:
        parts = pool.starmap(central_worker, [(ms, deadline, args.dps) for _, ms in tasks])
    out = {"mode": "central", "job": args.job, "jobs": args.jobs, "workers": args.workers,
           "start": args.start, "stop": args.stop, "lanes": parts}
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


def lind_worker(i, ks, deadline, dps):
    N, K = lind_member(i)
    t = comb(N, K)
    plist = primes_upto(N)
    elist = [carries(K, N - K, p) for p in plist]
    logt = log_of(t, dps)
    res, t0 = [], time.time()
    for k in ks:
        if time.time() > deadline:
            break
        s, u, c = solve_k(t, k, plist, elist, logt, dps)
        res.append([k, s, u, c])
    return {"i": i, "assigned_count": len(ks), "assigned_first": ks[0] if ks else None,
            "results": res, "seconds": time.time() - t0}


def run_lind(args):
    deadline = time.time() + args.minutes * 60
    N, K = lind_member(args.i)
    t = comb(N, K)
    kmax = kmax_bound(t) if args.kmax is None else args.kmax
    stride = args.jobs * args.workers
    lanes = [list(range(2 + args.job * args.workers + w, kmax + 1, stride))
             for w in range(args.workers)]
    with Pool(args.workers) as pool:
        parts = pool.starmap(lind_worker, [(args.i, ks, deadline, args.dps) for ks in lanes])
    out = {"mode": "lind", "i": args.i, "N": N, "K": K, "digits": len(str(t)), "kmax": kmax,
           "job": args.job, "jobs": args.jobs, "workers": args.workers, "lanes": parts}
    json.dump(out, open(args.out, "w"))
    found = [(r[0], r[1]) for p in parts for r in p["results"] if r[1]]
    print(f"lind i={args.i} job {args.job}: kmax={kmax}, hits (k, n): {found}")


# ----------------------------------------------------------------------------- merge


def run_merge(args):
    central, lind = {}, {}
    for path in args.files:
        d = json.load(open(path))
        for lane in d["lanes"]:
            if d["mode"] == "central":
                for r in lane["results"]:
                    central[r["m"]] = r
            else:
                for k, s, u, c in lane["results"]:
                    lind.setdefault(d["i"], {"kmax": d["kmax"], "N": d["N"], "K": d["K"],
                                             "digits": d["digits"], "k": {}})["k"][k] = s
    report = {}
    if central:
        m = min(central)
        while m + 1 in central:
            m += 1
        hits = {mm: r["solutions"] for mm, r in central.items() if r["solutions"]}
        report["central"] = {"contiguous_from": min(central), "contiguous_to": m,
                             "values_done": len(central), "hits": hits,
                             "exact_checks": sum(r["exact_checks"] for r in central.values()),
                             "primes_used": sum(r["primes_used"] for r in central.values())}
    for i, d in sorted(lind.items()):
        k = 1
        while k + 1 in d["k"]:
            k += 1
        hits = {kk: s for kk, s in d["k"].items() if s}
        report[f"lind_{i}"] = {"N": d["N"], "K": d["K"], "digits": d["digits"],
                               "kmax": d["kmax"], "k_contiguous_to": k, "hits": hits,
                               "complete": k >= d["kmax"]}
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
        got = []
        for k in range(2, kmax_for(t) + 1):
            s, _, _ = solve_k(t, k, ps, es, log_of(t, 60))
            assert s == brute_k(t, k), (t, k)
            assert solve_k(t, k, ps, es)[0] == s, (t, k)
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
    print(f"{args.random} random binomial coefficients agree with the unfiltered search")
    # 3. Central coefficients: Kummer valuations and the unfiltered search agree.
    for m in range(2, args.central + 1):
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
            s, _, _ = solve_k(t, k, plist, elist, log_of(t, 60))
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
    for a in ("--start", "--stop", "--job", "--jobs", "--workers"):
        c.add_argument(a, type=int, required=True)
    c.add_argument("--minutes", type=float, default=60)
    c.add_argument("--dps", type=int, default=60)
    c.add_argument("--out", required=True)
    l = sub.add_parser("lind")
    for a in ("--i", "--job", "--jobs", "--workers"):
        l.add_argument(a, type=int, required=True)
    l.add_argument("--kmax", type=int)
    l.add_argument("--minutes", type=float, default=60)
    l.add_argument("--dps", type=int, default=60)
    l.add_argument("--out", required=True)
    g = sub.add_parser("merge")
    g.add_argument("files", nargs="+")
    g.add_argument("--out", required=True)
    args = ap.parse_args()
    {"selftest": run_selftest, "central": run_central, "lind": run_lind,
     "merge": run_merge}[args.mode](args)


if __name__ == "__main__":
    main()
