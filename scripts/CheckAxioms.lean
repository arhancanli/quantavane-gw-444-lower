module

import Solution

/-!
# Axiom check

`lake env lean scripts/CheckAxioms.lean` (after `lake build`) prints the axioms that each compared
theorem of `Solution.lean` depends on. Palomar permits only `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms Gw444.exists_good
#print axioms Gw444.lt_of_gwProperty
#print axioms Gw444.lt_GW
#print axioms Gw444.exists_canonical
