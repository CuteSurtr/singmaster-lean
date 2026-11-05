"""Concatenate library files into one file for live.lean-lang.org."""
import re, sys
out = ["import Mathlib\n"]
for path in sys.argv[2:]:
    src = open(path).read()
    src = re.sub(r"\A/-.*?-/\n", "", src, flags=re.S)          # license header
    src = "\n".join(l for l in src.splitlines() if not l.startswith("import ")) + "\n"
    out.append(f"\n-- ===== {path.split('/')[-1]} =====\n" + src)
open(sys.argv[1], "w").write("".join(out))
