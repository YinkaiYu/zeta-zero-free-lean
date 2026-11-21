import Solution
import Lean.Util.CollectAxioms

example :
    ∃ c : ℝ, 0 < c ∧ ∀ s : ℂ, s ≠ 1 →
      1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0 :=
  AlpogeRHCore1.zeroFreeRegion

open Lean in
run_cmd do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  for axiomName in ← collectAxioms ``AlpogeRHCore1.zeroFreeRegion do
    unless permitted.contains axiomName do
      throwError "unexpected axiom {axiomName}"

#print axioms AlpogeRHCore1.zeroFreeRegion
