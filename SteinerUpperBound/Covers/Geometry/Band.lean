module

public import SteinerUpperBound.Covers.Geometry.BandAggregate

@[expose] public section

/-!
# Retained band completeness

Namespace: `SteinerUpperBound.Covers.Geometry.BandCompleteness`.

The public parameters are `bandDelta = 1/10000000000` and
`bandTau = Structural.sigma0/100`.

## Pointwise API

`retained_band_witness I N ρ hc hNT hρ a ha hsmall hC hhigh` supplies an actual
`Y ⊆ C` with `2 ≤ |Y| ≤ 4`, an actual projected set with cardinality between
two and four contained in `N ∩ C`, and band candidate value at least `sigma0*a/2`.
Here `hC : C ∈ Structural.components I a` and
`hhigh : sigma0*a ≤ Structural.localAdvantage I C`.

`retained_band_completeness I N ρ hc hNT hρ a ha hsmall hC hphase hhigh`
additionally uses
`hphase : C ∉ phaseBad I I.terminals (a - 2*ρ) a`
and returns
* `N ∩ C ∈ componentsOn I N a`;
* `componentMap I I.terminals a (N ∩ C) = C`;
* `sigma0*a/2 ≤ Band.score I (N ∩ C) a ρ bandTau`.

`persistent_retained_injective` proves that different persistent exact
components map to different retained components.

The geometric inputs are only `hc : CoverOn I I.terminals N ρ`,
`hNT : N ⊆ I.terminals`, `hρ : 0 ≤ ρ`, `ha : 0 < a`, and
`hsmall : ρ ≤ bandDelta*a`. No scale-versus-horizon bound is needed.

## Aggregate API

`lambda_le_smallScore_and_bad I g N ρ hc hNT hρ hsmall BQ` proves

`Structural.lambda I g ≤ 2*totalSmallScore I g N ρ BQ / Structural.sigma0
  + weightedPhaseBad I g ρ + weightedLarge I g N BQ`.

`N` and `ρ` are indexed by `Fin (g.intervals+1)`; the four geometric hypotheses
hold coordinatewise. `BQ : ℕ` is arbitrary. `totalSmallScore` sums the actual
`Band.score` over retained components of cardinality at most `BQ`;
`weightedLarge` counts all retained components larger than `BQ`, weighted by
the corresponding scale. The phase-bad term depends only on exact-terminal
thresholds, not on the retained sets.

## Proved losses

The generic `band_candidate_lower` loses at most `65*ρ + 3*(τ*a)`.
`projected_gain_eq` proves exact contraction-gain invariance for `t > ρ`.
`localCost_projected_le` proves a `50*ρ` one-center cost loss from an actual
attained network: its endpoints lie in at most five vertices and hence it
has at most 25 possible edges. No clean-network or saving certificate is
assumed. `benefit_eq_integral_to_component` proves both horizon tails zero,
so no hidden horizon hypothesis remains.
-/
