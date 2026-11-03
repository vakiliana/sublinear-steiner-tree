module

public import SteinerUpperBound.SmallCoverProgram.Closure.Program
public import SteinerUpperBound.SmallCoverProgram.Closure.Roots

/-!
Boolean dense-array connectivity closure on `Fin g`. The actual ticked program
performs `Nat.log2 (g+1)+1` squaring rounds. `computed_correct` proves exact
graph reachability; `computed_work` gives `32*g^3*(1+log2(g+1))` work for
`g ≥ 1`, and `computed_resources` proves that no oracle queries are made.
`roots`/`rootsRun` compute minimum-index component IDs in another `O(g^2)`
charged scan; `computed_roots_partition`, `computed_roots_bound`, and
`computed_roots_min` prove the actual root vector's partition and canonicality.
-/

@[expose] public section

namespace SteinerUpperBound.SmallCoverProgram.Closure

end SteinerUpperBound.SmallCoverProgram.Closure
