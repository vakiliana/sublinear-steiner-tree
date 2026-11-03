module

import SteinerLowerBound
import SteinerUpperBound
meta import Lean.Util.CollectAxioms

#print axioms SteinerLowerBound.lower_bound
#print axioms SteinerLowerBound.epsilon_lower_bound
#print axioms SteinerUpperBound.upper_bound
#print axioms SteinerUpperBound.upper_bound_original_probability
#print axioms SteinerUpperBound.algorithm_query_time_bound

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let count ← (← getEnv).constants.foldM (init := (0 : Nat)) fun count name _info => do
    let text := name.toString
    let project := (`SteinerLowerBound).isPrefixOf name || (`SteinerUpperBound).isPrefixOf name ||
      text.startsWith "_private.SteinerLowerBound." || text.startsWith "_private.SteinerUpperBound."
    if !project then
      return count
    for axiomName in ← Lean.collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on unapproved axiom {axiomName}"
    return count + 1
  logInfo m!"Audited {count} project declarations; only standard Lean axioms are permitted."
