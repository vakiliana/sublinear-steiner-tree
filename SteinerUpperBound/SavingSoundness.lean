module

public import SteinerUpperBound.SavingSoundness.Grid
public import SteinerUpperBound.SavingSoundness.SupportRank
public import SteinerUpperBound.SavingSoundness.PortList

/-!
# Soundness of the actual retained-row saving

`retained_saving_sound` proves the manuscript bound
`∑ i, aᵢ * savingOn I (N i) aᵢ (5*aᵢ/8) ≤ 32*Qs*(I.mst-I.optimum)`
for an actual `Structural.Grid`, actual retained subsets of the terminals,
and deterministic covers at radius `delta*aᵢ`, where `delta = 10⁻¹⁰`.
Its only additional hypotheses are `0 < Qs` and the stated geometric
separation `(5/4)*omega^(-Qs) < 1-2*delta`.
`retained_saving_sound_32` discharges those numerical conditions with `Qs=32`.
`grid_soundness` permits any nonnegative `δ` with `64*δ ≤ 1`.

No charged networks, forest, partition-rank identity, or lower-benefit
certificate is supplied as a hypothesis. `exists_scale_networks` constructs
the actual terminal-clique links and metric stars from
`SetSystem.saving_forest_on_universe`, choosing true ball-incidence terminals.
`partition_gain` proves their quotient rank using the actual retained
projection and complete fibers. `separated_sound` telescopes the actual rank
gains and applies `Network.integral_lifting`. Residue lists then give the grid
bound. Zero-saving scales use empty networks, so there is no artificial
restriction requiring every grid scale to be below the integration horizon.

`rank_map_eq_of_injOn_support` is a separate generic support-restriction
interface for structural event labels. `port_rank_saving_list` applies the
same saving bound to an actual list-fold union of port cliques, counting list
positions and permitting repeated center IDs.
-/

@[expose] public section

namespace SteinerUpperBound.SavingSoundness

end SteinerUpperBound.SavingSoundness
