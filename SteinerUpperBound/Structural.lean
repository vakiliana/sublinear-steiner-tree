module

public import SteinerUpperBound.Structural.Statistics
public import SteinerUpperBound.Structural.LocalCost
public import SteinerUpperBound.Structural.Cuts
public import SteinerUpperBound.Structural.Rooted
public import SteinerUpperBound.Structural.Shapes
public import SteinerUpperBound.Structural.Regions
public import SteinerUpperBound.Structural.Exchange
public import SteinerUpperBound.Structural.Cleanup
public import SteinerUpperBound.Structural.Suppression
public import SteinerUpperBound.Structural.CompleteCleanup
public import SteinerUpperBound.Structural.Reduction
public import SteinerUpperBound.Structural.TreeCuts
public import SteinerUpperBound.Structural.Cherries
public import SteinerUpperBound.Structural.CherryElimination
public import SteinerUpperBound.Structural.Components
public import SteinerUpperBound.Structural.Limbs
public import SteinerUpperBound.Structural.Stars
public import SteinerUpperBound.Structural.FringeEvidence
public import SteinerUpperBound.Structural.Promotion
public import SteinerUpperBound.Structural.RegionOperations
public import SteinerUpperBound.Structural.Fans
public import SteinerUpperBound.Structural.FanPromotion
public import SteinerUpperBound.Structural.FanPromotionResult
public import SteinerUpperBound.Structural.FanPromotionConstruction
public import SteinerUpperBound.Structural.FanElimination
public import SteinerUpperBound.Structural.Topology
public import SteinerUpperBound.Structural.FringeGroups
public import SteinerUpperBound.Structural.PromotionBounds
public import SteinerUpperBound.Structural.RegularData
public import SteinerUpperBound.Structural.CherryData
public import SteinerUpperBound.Structural.BatchPromotion
public import SteinerUpperBound.Structural.StarBatchData
public import SteinerUpperBound.Structural.StarBatchCuts
public import SteinerUpperBound.Structural.DirectReconnection
public import SteinerUpperBound.Structural.StarReconnection
public import SteinerUpperBound.Structural.StarBounds
public import SteinerUpperBound.Structural.CoreFrames
public import SteinerUpperBound.Structural.CoreConstructions
public import SteinerUpperBound.Structural.TerminationGeometry
public import SteinerUpperBound.Structural.EventAvailability
public import SteinerUpperBound.Structural.GridScales
public import SteinerUpperBound.Structural.StarRankBridge
public import SteinerUpperBound.Structural.Ledger
public import SteinerUpperBound.Structural.LedgerUpdates
public import SteinerUpperBound.Structural.StarRecording
public import SteinerUpperBound.Structural.PromotionRecording
public import SteinerUpperBound.Structural.Process
public import SteinerUpperBound.Structural.Theorem

/-!
# Finite-tree structural elimination

`Structural.structural_bound` and `Structural.negative_evidence` concern the actual network
optimum and terminal MST. Their only grid hypothesis is numerical endpoint coverage, with
positivity and the geometric ratio stored in `Structural.Grid`.

The proof constructs star reconnections and fringe promotions, preserves terminal edges,
and inducts on the number of nonterminal edges. `Structural.optimal_elimination_charges`
exports the resulting terminal tree and its charged histories; no trace is assumed.
-/

@[expose] public section
