module

public import SteinerUpperBound.PortGraph.RuntimeAdapter.Value

@[expose] public section

/-!
# Concrete cached metric callbacks for the actual lazy matching runtime

Namespace: `SteinerUpperBound.PortGraph.RuntimeAdapter`.
Only public `LocalAccess.SlotConfig`, frame data, cache, array lengths/caps, and
the public integer rank size are runtime inputs. No metric `Instance`, latent
retained set, true-edge carrier, or desired VO correctness/cost certificate is
an input of the code.

## Code and memory

`Memory Q n b B` contains a public-root indexed optional vector of prepared
frames, the supplied seed frame, and the retention cache.
`initial frame cache` stores `frames=none`: it allocates NO indexed array.
The first actual `prepare` allocates `Vector.replicate n none`, seeds the
supplied frame at its public head, and charges `n+8` work for initialization.

`prepare` checks the indexed frame table and only calls actual
`LocalAccess.locateProgram` on a miss. `slot` NEVER prepares or initializes;
it calls actual `LocalAccess.slotProgram` on the ready cached frame. Successful
partner replies carry their already canonical prepared frame, which is stored
at `reply.otherRoot`. Explicit ticks charge table lookup/branching, cache
replacement, frame insertion, and encoding.

`primitives cfg frame cache` instantiates
`Matching.Padded.Runtime.Primitives (length n b B k) (Name n) (Sym2(Fin n)) Q`,
where the ambient root length is the constant `b*B*k`.
Its actual code has exact deterministic `prepare_evaluates` and
`slot_evaluates` interfaces, not an assumed callback law.

`oracle cfg Nstar frame cache` calls the ACTUAL `Runtime.answer` at the
canonical frame head and returns its Boolean together with the primitive
memory's updated retention cache. Rank/matching memo is fresh per invocation.
The D-aware entrypoint is
```
builder key scale terminals B :
  (D : Vector Bool n) → (d : ℕ) →
    Frame n d B → Cache Q → Code(Sym2(Fin n)) Q (Bool × Cache Q).
```
It constructs the actual SlotConfig with the newly supplied bitmap and row cap.

## Persistent correctness and generic interface instantiation

`Inv` proves the cache correct and every stored frame canonical at the public
root embedding of a genuine residual small component. `Ready memory C`
asserts that component's canonical frame is already indexed in the table.
`prepare_correct` establishes readiness and preserves ALL previous ready
components. `slot_correct` gives the exact encoded static test and preserves
`Inv` and all previous readiness.

`presentation I bits cfg hT hnd P Nstar hN` supplies the actual PortGraph root
and physical-copy embeddings. `contract ... frame cache C0 hf hc` constructs
`Presentation.Contract` from those proved metric facts; it needs only the
public terminal equality/nodup, `hf : frame = canonicalFrame C0`, and correct
incoming cache. `deterministic` constructs `Presentation.Deterministic`.
There is no final matching value/time premise.

`prepare_initial_evaluates` proves initial preparation costs EXACTLY `n+12`
and makes zero metric queries, retention queries, or positive replies: the
already supplied canonical frame is reused, not prepared again.
`prepare_ready_evaluates` is an EXACT four-work, zero-query cache hit.
`slot_partner_ready` and `prepare_partner_evaluates` prove accepted partners'
carried frames make later preparations four-work hits as well.

## Honest per-access accounts

The checked natural-counter bounds are:
```
hot prepare hit:  work = 4, no queries/positives
any preparation: work ≤ n+20+locateBudget, positives ≤ B
ready slot:      work ≤ 2B+76+Heavy*partnerBudget
                 positives ≤ Heavy*(B+2).
```
The extra twelve slot work units explicitly charge the adapter's table/cache
operations; no hidden free table operations or overhead credit is assumed.
`Heavy` is the parent's actual fixed-world predicate.

`workAccount` and `positiveAccount` construct genuine `Padded.Account`s.
`workResources` and `positiveResources` instantiate the matching owner's
`Presentation.Resources` with ordinary counter `(1,0,0,0)` and disclosure
counter `(0,0,0,1)`. Bounds are fixed before rank randomness and uniform over
all valid incoming primitive memories.

The ordinary `workCap` dominates preparation and every slot; `workCap_le`
reduces it to `2100*(n+1)*(B+2)^2` under `k≤n` and `b²≤50*(n+1)`.
The disclosure account has `Cstar=B+2` and arithmetic rate zero.
Final weighted whole-VO accounting remains matching-owner work.

## Derived actual Boolean/cache kernel

`publicSize n k b B = n*(b*B*k+1)+2` is entirely public. `parameters` PROVES
the genuine model size bound `|Vertex|+totalSlots+2≤publicSize`.
The wrapper uses that size, with no unknown retained cardinality.

`oracle_mean_error` and `oracle_event_error` instantiate the matching owner's
checked actual-code `ValueKernel` theorem with this concrete adapter.
The comparison is against the uniform strict order of the SAME true labeled
port copies, with explicit error `1/publicSize^30`. `strictMean` and
`strictProbability` are generic finite-rank-instance wrappers for that law.
No unconditional no-tie assumption or collapsed simple-copy graph is used.

`oracle_preserves` is the generic actual-code `Causal.Ensures` returned-cache
guarantee, and `oracle_cache_failure_zero` states its zero bad-cache
probability/indicator expectation, on genuine canonical frames.
This does not claim a stronger theorem about forged-frame counterfactual
branches. `oracle_counter` proves the wrapper adds EXACTLY
`12*counter.work` to the actual Runtime.answer expected counter, and thus adds
no metric, retention, or positive-reply cost.
-/
