"""Generate column certificates for Singmaster/Certified.lean.

For a value t and its known positions S (with 2 <= k, 2k <= n), column k in 2..kmax gets the
certificate a = largest n with C(n, k) < t.  If (a + 1, k) is in S then C(a + 1, k) = t and we
need t < C(a + 2, k); otherwise we need t < C(a + 1, k).  kmax is the largest k with
C(2k, k) <= t.
"""
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


if __name__ == "__main__":
    out = {}
    small = {
        120: [(16, 2), (10, 3)],
        210: [(21, 2), (10, 4)],
        1540: [(56, 2), (22, 3)],
        7140: [(120, 2), (36, 3)],
        11628: [(153, 2), (19, 5)],
        24310: [(221, 2), (17, 8)],
        3003: [(78, 2), (15, 5), (14, 6)],
    }
    for t, S in small.items():
        km, as_, found = cert(t, S)
        assert all(comb(n, k) == t for n, k in S)
        print(f"t={t} kmax={km} as={lean_list(as_)}")
    for (N, K) in [(104, 39), (714, 272), (4895, 1869)][: int(sys.argv[1]) if len(sys.argv) > 1 else 2]:
        t = comb(N, K)
        assert t == comb(N - 1, K + 1)
        km, as_, found = cert(t, [(N, K), (N - 1, K + 1)])
        s = lean_list(as_)
        print(f"lind N={N} K={K} digits={len(str(t))} kmax={km} cert_chars={len(s)}")
        with open(f"lind_{N}_{K}.txt", "w") as f:
            f.write(str(t) + "\n" + s + "\n")
