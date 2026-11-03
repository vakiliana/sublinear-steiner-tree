module

public import SteinerUpperBound.Covers.Basic
public import SteinerUpperBound.Covers.Independent
public import SteinerUpperBound.Covers.Actual
public import SteinerUpperBound.Covers.SamplingTree
public import SteinerUpperBound.Covers.GlobalCap
public import SteinerUpperBound.Covers.MetricOracle
public import SteinerUpperBound.Covers.DisclosureBudget
public import SteinerUpperBound.Covers.ProposalCap
public import SteinerUpperBound.Covers.Scales
public import SteinerUpperBound.Covers.Geometry.Band
public import SteinerUpperBound.Covers.Geometry.BandSoundness
public import SteinerUpperBound.Covers.OracleProgram
public import SteinerUpperBound.Covers.OracleProgramMean

@[expose] public section

/-!
# Independent covers and finite implicit sampling

All interfaces are in `SteinerUpperBound.Covers`.

* `actual_cover_at_radius_budget` constructs the independent, fixed-root
  retention law from private finite uniform-terminal tapes. `actual_all_scales`
  gives the finite-union guarantee with independent randomness across scales.
  The proofs use minimum-original-degree deletion, actual terminal-MST packing,
  and binary hop-ball growth. Thus `h = floor(log₂ k) + 1`,
  `ψ = ceil(2 log(4km/β))`, and the size threshold is
  `exp(1) (1 + ψ (1 + 2h·mst/ρ)) + log(4m/β)`.
* `Factory.distanceTree_output` and `distanceTree_queries_le_draws` identify
  the actual metric-query procedure. `private_tapes`, `family_private_tapes`,
  `expanded_cached_law`, and `global_capped_law_close` prove its finite-tape,
  cached, and globally capped semantics. `cached_bits_ideal_close` accounts
  for private-tape exhaustion.
* `Factory.cached_factory_cap_tail` proves
  `Pr[global cap ∧ new retained disclosures ≤ a] ≤ exp(a - B/(2k))`
  directly for the cached interpreter. `work_le`, `pending_work_eq`,
  `new_disclosures_le_positiveHeight`, and `sampler_factory_cap_budget` concern
  its actual counters; fixed positive cache entries are not charged again.
* `Rejection.pool_success_atom` proves exact iid uniform-retained labels
  conditional on successful rejection rows. `capped_sampler_uniform_budget`
  transfers to the fixed-proposal implementation with total-variation error
  at most `β`. `capped_sampler_and_calibration` proves successful sampling and
  `(1-ξ)g ≤ g₋ ≤ g ≤ g₊ ≤ (1+ξ)g`, using actual stopping counts.
  The implementation uses only membership queries. `cappedPoolTree_proposals`
  counts its proposals exactly, and `cachedSampler_resources` proves cached
  disclosure bounds.

Calibration deliberately uses the allowed Chebyshev alternative:
`s = ceil(512/(β ξ²))`, rather than a logarithmic dependence on `1/β`.
The final proposal cap is `ceil(4k(s + log(2/β)))`; row caps are only a finite
reference construction, and introduce no extra factor in executed proposals.
No cover, sampler-law, independence, or stochastic work certificate is assumed.
-/
