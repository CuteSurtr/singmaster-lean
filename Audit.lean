import Singmaster

/-!
# Axiom audit

This file fails to build if a result listed below depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound`. That excludes `sorryAx` and the `Lean.ofReduceBool` axiom
that `native_decide` adds. The finite checks (`Singmaster.small_rows_3003` and the certificates
in `Singmaster.Collisions` and `Singmaster.Central`) use `decide +kernel`, which adds no axiom.
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
  Singmaster.choose_eq_choose_pred_succ_iff_fib
  Singmaster.singmaster.variants.ncard_le_two_mul_log
  Singmaster.exists_centralBinom_of_odd_ncard
  Singmaster.exists_centralBinom_of_ncard_eq_five_or_seven
  Singmaster.odd_ncard_iff
  Singmaster.pow_le_factorial_mul_choose_le
  Singmaster.prime_dvd_choose_iff_window
  Singmaster.central_window
  Singmaster.choose_eq_window
  Singmaster.ncard_prime
  Singmaster.ncard_choose_prime_two
  Singmaster.singmaster.variants.infinite_ncard_eq_two
  Singmaster.singmaster.variants.infinite_ncard_eq_four
  Singmaster.ncard_eq_of_certOK
  Singmaster.ncard_120
  Singmaster.ncard_210
  Singmaster.ncard_1540
  Singmaster.ncard_7140
  Singmaster.ncard_11628
  Singmaster.ncard_24310
  Singmaster.ncard_choose_104_39
  Singmaster.ncard_choose_714_272
  Singmaster.ncard_choose_4895_1869
  Singmaster.ncard_solutions_fib_2
  Singmaster.ncard_solutions_fib_3
  Singmaster.ncard_solutions_fib_4
  Singmaster.ncard_centralBinom
  Singmaster.ncard_ne_five_and_ne_seven
