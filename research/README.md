# Singmaster research archive

This directory preserves the local research notes, search programs, certificates,
and computational records collected through 25 October 2026. It was added to the
repository on 6 November 2026. The original research files are retained unchanged;
this is an archive of progress, not a new proof or a new verification run.

## Reading the archive

- [NOTES.md](NOTES.md) records successive sessions and the completed search runs.
  Later entries supersede earlier partial results and plans.
- [WRITEUP.md](WRITEUP.md) and [LITERATURE.md](LITERATURE.md) are working research
  documents. Their historical-novelty claims remain provisional. In particular,
  the writeup's comparison with searches through one million rows does not by
  itself establish novelty for Lind values whose row indices are 714 and 4,895.
- [search/](search/) contains search code, workflow snapshots, and retained JSON
  evidence. The workflow snapshots are documentation and are not installed as
  active GitHub Actions workflows.
- [cert/](cert/) contains certificate-generation experiments, and
  [drafts/Parity.lean](drafts/Parity.lean) is a historical draft, not the current
  formal proof target.

## Verification status

The [project README](../README.md) describes the Lean formalization, including
the exact multiplicity of 3003, the Lind family and its converse, parity, exact
sixfold counts through the fourth Lind value, and the central-binomial check
through index 200. The build targets and axiom audit remain unchanged by this
archive commit.

The later search records report central-binomial coverage through index 212,000
and exact sixfold counts for the eighth and ninth Lind values. These larger
computations are not covered by the Lean-certified range. The original run
identifiers, coverage details, and limitations are recorded in NOTES.md and the
JSON evidence. The corresponding search history is also retained on the
[search branch](https://github.com/CuteSurtr/singmaster-lean/tree/search).

No general resolution of Singmaster's conjecture is claimed. Adding this archive
does not independently re-establish mathematical correctness or historical
priority. The archival checks cover file integrity, JSON parsing, and Python
syntax; they do not rerun the searches or the Lean build.
