module

public import SteinerUpperBound.FiniteMST.Compiled

/-!
# Actual finite weighted MST evaluator

`FiniteMST.program d` takes only a dense observed real matrix on `Fin m`.
The undirected weight reads the upper-triangular entry; input symmetry is not
required.
It generates each unordered pair once in charged loops, performs actual
insertion sorting by observed weights, and runs Kruskal, recomputing the
checked Boolean connectivity closure before every candidate. Accepted edge
weights are added to an actual scalar accumulator.

`program_correct` proves equality with `TerminalMST.value (weight d) univ`
for every nonnegative matrix, without metric assumptions. `on_labels_correct`
bridges injective vertex labels and agreement on off-diagonal entries to the
actual MST on their image. Diagonal weights are irrelevant to that bridge.

`program_evaluates` identifies `run`; `compiled_spec` proves the same result
for every compiled seed, with zero oracle/retention queries and positive
replies, and work at most `512*(m+1)^6*(1+Nat.log2(m+1))`.
No optimizer, spanning forest, sorted-order certificate, or full metric
instance is an input to the runtime program.
-/

@[expose] public section

namespace SteinerUpperBound.FiniteMST

end SteinerUpperBound.FiniteMST
