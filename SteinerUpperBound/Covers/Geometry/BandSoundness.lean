module

public import SteinerUpperBound.Covers.Geometry.BandSoundnessGrid

@[expose] public section

/-!
# Actual retained band soundness

Namespace: `SteinerUpperBound.Covers.Geometry.BandSoundness`.
The constants are `BandCompleteness.bandDelta = 1/10000000000` and
`BandCompleteness.bandTau = Structural.sigma0/100`.

## Exact public API

`retained_band_sound I g N hN hc Qq hQq hsep` proves

`(∑ i, ∑ C ∈ componentsOn I (N i) (g.scale i),
    Band.score I C (g.scale i) (bandDelta*g.scale i) bandTau)
  ≤ (Qq : ℝ) * (I.mst - I.optimum)`.

Its inputs are:
* `g : Structural.Grid`;
* `N : Fin (g.intervals+1) → Finset V`;
* `hN : ∀ i, N i ⊆ I.terminals`;
* `hc : ∀ i, CoverOn I I.terminals (N i) (bandDelta*g.scale i)`;
* `Qq : ℕ`, `hQq : 0 < Qq`;
* `hsep : Structural.omega ^ (-(Qq : ℤ)) < bandTau/2`.

`small_retained_band_sound I g N hN hc BQ Qq hQq hsep` gives the same right-hand
side for `BandCompleteness.totalSmallScore` at the actual radii.
`grid_soundness` additionally allows arbitrary radii `0 ≤ ρ_i ≤ bandDelta*a_i`.

## Actual witnesses and charging

`score_network_exists` constructs a genuine attaining small set and an attained
one-center optimizer for every positive score; zero scores use empty networks.
`local_band_le_global` proves the `6ρ` band-comparison loss by the bottleneck
reachability theorem, an exact quotient-clique gain formula, and translation
of the rank-at-most-three contraction curve. The score's own `6ρ` penalty
absorbs this loss exactly.

`retained_quotient_disjoint` proves that different retained components touch
disjoint actual terminal threshold components below `a-2ρ`.
`gain_disjoint_cliques` and `cell_gain_additive` prove genuine rank additivity
using `SetSystem.quotient_gain` and disjoint coordinate supports.

`separated_sound` proves coefficient one for a separated list of scales.
It uses disjoint integration bands and one global union network, not an
assumed marginal telescoping statement. Its integration horizon is explicitly
constructed above both every scale and every terminal distance.
`grid_scale_band_separated` discharges disjointness from the actual grid ratio;
residue partitioning then gives the exact factor `Qq`, with no additional
absolute multiplier.

No phase-persistence hypothesis, scale-versus-horizon bound, supplied network
certificate, supplied benefit certificate, or probabilistic independence
assumption is needed.
-/
