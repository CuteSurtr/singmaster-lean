"""Prototype of the divisor-witness column certificate.

For column k and t: F = k!, T = F*t. lo = least n with n^k >= T, hi = largest n with
(n+1-k)^k <= T. Any x with hi - k < x <= lo lies in every window (n-k, n], n in [lo, hi], so a
solution needs x | T. A column is excluded by one x with T % x != 0.
"""
import sys, time
from math import comb, factorial

def iroot(a, k):
    """floor(a^(1/k)) for a >= 0."""
    if a < 2:
        return a
    x = 1 << ((a.bit_length() + k - 1) // k)
    while True:
        y = ((k - 1) * x + a // x ** (k - 1)) // k
        if y >= x:
            break
        x = y
    while x ** k > a:
        x -= 1
    while (x + 1) ** k <= a:
        x += 1
    return x

def column(t, k, F):
    T = F * t
    r = iroot(T, k)
    lo = r if r ** k >= T else r + 1           # least n with n^k >= T
    hi = r + k - 1                              # largest n with (n+1-k)^k <= T
    while (hi + 2 - k) ** k <= T:
        hi += 1
    while hi >= k - 1 and (hi + 1 - k) ** k > T:
        hi -= 1
    assert (lo - 1) ** k < T < (hi + 2 - k) ** k
    for x in range(lo, max(hi - k, 0), -1):     # x in (hi - k, lo]
        if x > 0 and T % x != 0:
            return ("wit", lo, hi, x)
    return ("gap", lo, hi)

def run(t, kmax, S=()):
    F = 1
    stats = {"wit": 0, "gap": 0, "gapcost": 0}
    for k in range(2, kmax + 1):
        F *= k
        c = column(t, k, F)
        stats[c[0]] += 1
        if c[0] == "gap":
            stats["gapcost"] += k
    return stats

if __name__ == "__main__":
    what = sys.argv[1]
    if what == "central":
        M = int(sys.argv[2])
        tot = {"wit": 0, "gap": 0, "gapcost": 0}
        t0 = time.time()
        for m in range(2, M + 1):
            st = run(comb(2 * m, m), m)
            for key in tot:
                tot[key] += st[key]
        print("central M=%d" % M, tot, "time %.1fs" % (time.time() - t0))
    else:
        i = int(sys.argv[2])
        fib = [0, 1]
        while len(fib) < 2 * i + 5:
            fib.append(fib[-1] + fib[-2])
        N, K = fib[2 * i + 2] * fib[2 * i + 3], fib[2 * i] * fib[2 * i + 3]
        t = comb(N, K)
        km = 1
        while comb(2 * (km + 1), km + 1) <= t:
            km += 1
        t0 = time.time()
        print("lind i=%d N=%d K=%d kmax=%d" % (i, N, K, km), run(t, km), "time %.1fs" % (time.time() - t0))
