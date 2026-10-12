import Singmaster

/-!
# Axiom audit

This file fails to build if a result listed below depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound`. That excludes `sorryAx` and the `Lean.ofReduceBool` axiom
that `native_decide` adds. The finite check in `Singmaster.small_rows_3003` uses `decide +kernel`,
which adds no axiom.
-/

open Lean Elab Command in
/-- `#assert_standard_axioms n₁ n₂ ...` fails if a declaration depends on a nonstandard axiom. -/
elab "#assert_standard_axioms " ids:ident* : command => do
  for id in ids do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
    let axioms ← liftCoreM <| collectAxioms name
    for ax in axioms do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwErrorAt id "{name} depends on {ax}"

#assert_standard_axioms
  Singmaster.solutions_finite
  Singmaster.solutions_3003
  Singmaster.singmaster.variants.ncard_3003
  Singmaster.eight_le_of_bound
  Singmaster.choose_fib_eq
  Singmaster.six_le_ncard_solutions_fib
  Singmaster.singmaster.variants.infinite_six_le_ncard
