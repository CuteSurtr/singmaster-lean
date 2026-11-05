import sys
from math import comb
from gencert import cert, lean_list

M = int(sys.argv[1])
entries = []
cost = 0
for m in range(2, M + 1):
    t = comb(2 * m, m)
    km, as_, found = cert(t, [(2 * m, m)])
    assert km == m and len(as_) == m - 1 and not found
    entries.append(f"({t}, {lean_list(as_)})")
    cost += sum(2 * k for k in range(2, m + 1))
body = ",\n    ".join(entries)
with open(f"central_{M}.txt", "w") as f:
    f.write("[" + body + "]\n")
print(M, "chars", len(body), "approx kernel steps", cost, "bound digits", len(str(comb(2 * M + 2, M + 1))))
