# Quorum Domain Proof Review — Iteration 2

Reviewed:

- `src/domain.ts`
- `src/domain.dfy`
- `src/domain.dfy.gen`
- `DESIGN_QUORUM.md`
- prior review: `PROOF_FINDINGS.md`

Verification status checked locally:

```sh
dafny verify quorum/src/domain.dfy
```

Result: `142 verified, 0 errors`.

## Executive Summary

Iteration 2 materially strengthens the proof story. The domain proofs now cover the original aggregate core plus several gaps called out in the first review:

- paint/update monotonicity,
- standalone participant-id uniqueness preservation lemmas,
- membership facts for `freeParticipants`,
- implemented `participantsAt`,
- implemented `overlap`,
- event-level sparse encode/decode round-trip,
- and query-over-export soundness for `heatmap` and `isBest`.

The safest high-level claim is now:

> For well-formed events, the verified domain core proves exact heatmaps, exact positive-argmax best masks, exact threshold masks, invariant-preserving mutations/replay for the implemented structural invariant, participant-order-independent heatmaps, same-`pid` LWW commutativity for distinct timestamps, monotonicity under joins and availability-expanding paints, exact event-level sparse codec round-trip, and export-preservation for `heatmap` and `isBest`.

However, the proofs still do not fully capture the complete product/design promise as written in `DESIGN_QUORUM.md`. The main remaining gaps are:

- `wellFormed` still excludes A2 participant-id uniqueness.
- `applyOp`/`replay` preserve only A1+A3, not uniqueness.
- join operations can still introduce duplicate ids.
- `participantsAt` is only proved count-consistent with the heatmap, not membership-exact.
- `overlap` is proved to match the implemented predicate, but the predicate is existential per id and has surprising behavior with duplicate ids and empty `pids`.
- query-over-export is proved for `heatmap` and `isBest`, but not for `availableAtLeast`, `participantsAt`, or `overlap`.
- the export proof is for in-memory `SparseEvent` values, not NDJSON bytes, parser behavior, streaming format, SQL, D1, or R2.
- arbitrary op-log convergence is still not proved.
- design-doc claims about `src/grid.ts`, app files, `npm test`, and VC counts do not match this workspace snapshot.

## What Improved Since Iteration 1

### Paint Monotonicity Is Now Proved

The first review found that “marking more slots never lowers counts” was not proved. Iteration 2 adds:

- `isSubsetOf`
- `freeAtMonotone`
- `countFreeMonotoneSetAvail`
- `heatmapMonotoneUnderPaint`

The proved statement is strong enough for the intended monotonicity claim when the incoming availability is a superset of every matching participant row:

```ts
//@ requires wellFormed(e) && newAvail.length === e.numSlots
//@ requires forall(i, 0 <= i && i < e.participants.length && e.participants[i].id === pid ==>
//@           isSubsetOf(e.participants[i].avail, newAvail) === true)
//@ ensures forall(s, 0 <= s && s < e.numSlots ==>
//@           heatmap(setAvailability(e, pid, newAvail))[s] >= heatmap(e)[s])
```

Important nuance: `setAvailInList` updates only the first matching id, while the precondition quantifies over all matching ids. This is fine under unique ids, and still sound under duplicates if every duplicate row with that id is a subset of `newAvail`. But it is not a substitute for proving unique participant ownership.

### Standalone Id-Uniqueness Lemmas Exist

Iteration 2 adds:

- `uniqueIds`
- `uniqueIdsPreservedByJoin`
- `uniqueIdsPreservedBySetAvail`
- `uniqueIdsPreservedByRemove`
- `uniqueIdsPreservedByLWW`

These are useful building blocks. They prove that uniqueness can be preserved by specific list transforms when the necessary preconditions hold.

But A2 is still not part of `wellFormed`:

```ts
wellFormed(e) === e.numSlots >= 0 && allAvailLen(e.participants, e.numSlots)
```

So `applyOpPreservesInv` and `replayPreservesInv` do not guarantee uniqueness. `applyOp(join)` also does not check `!idTaken`, so replay can reach duplicate ids while still satisfying the verified invariant.

### `freeParticipants` Has Stronger Membership Facts

Iteration 2 adds `freeParticipantsMembership`, proving:

- every returned participant is free at `s`,
- every input participant free at `s` appears in the returned list.

This is a real improvement over the first iteration, where only length consistency was proved.

Remaining nuance: the lemma is about participant values, not stable ids or occurrence counts. It also does not give a corresponding exact theorem for `whoIsFree` directly, though that can be obtained by applying the list lemma to `e.participants`.

### `participantsAt` Exists, But Is Only Count-Proved

`participantsAt(e, s)` is now implemented through `freeIdList`, and the proof establishes:

- `participantsAt(e, s).length === heatmap(e)[s]`

It does not yet prove:

- every returned id belongs to a free participant,
- every free participant id is returned,
- returned ids are distinct,
- or the result is duplicate-free under a unique-id invariant.

So it is safe to claim count consistency, but not full membership-exact query soundness for ids.

### `overlap` Exists, With A Precise Implemented Semantics

`overlap(e, pids)` now returns a boolean mask with:

```ts
overlap(e, pids)[s] === allPidsFreeAt(e.participants, pids, s)
```

That is proved.

The implemented semantics are:

- `pidFreeAt(ps, pid, s)` is true if there exists some row with that id that is free at `s`.
- `allPidsFreeAt(ps, pids, s)` is true if every requested id has some free row at `s`.
- For an empty `pids` list, `allPidsFreeAt` returns true for every slot.

This is defensible, but it is not yet the stronger “overlap of this distinct subset of people” property unless uniqueness and requested-id validity are also enforced or proved.

### Event-Level Codec Round-Trip Is Now Proved

Iteration 2 adds:

- `SparseParticipant`
- `SparseEvent`
- `encodeParticipant` / `decodeParticipant`
- `encodeParticipants` / `decodeParticipants`
- `encodeEvent` / `decodeEvent`
- `participantRoundTrip`
- `participantsListRoundTrip`
- `eventRoundTrip`

For `wellFormed(e)`, Dafny proves:

```ts
decodeEvent(encodeEvent(e)) === e
```

This closes a major gap from iteration 1 at the in-memory model level.

Scope limitation: this is not an NDJSON proof. It does not cover byte serialization, parse errors, field omission, schema evolution, streaming, SQL tables, D1, R2, or endpoint behavior.

### Query-Over-Export Is Proved For Heatmap And Best

Iteration 2 adds:

- `heatmapOverExport`
- `isBestOverExport`

For `wellFormed(e)`, these prove that encoding and decoding preserves:

- `heatmap(e)` pointwise,
- `isBest(e)` pointwise.

This is a real E2-style result, but narrower than the design-doc wording. There are no corresponding proved lemmas for:

- `availableAtLeast`,
- `whoIsFree`,
- `participantsAt`,
- or `overlap`.

## What The Proofs Safely Guarantee

### Aggregation

For any event with `e.numSlots >= 0`:

- `heatmap(e).length === e.numSlots`
- every heatmap entry equals `countFree(e.participants, s)`
- every heatmap entry is between `0` and `e.participants.length`

This does not require `wellFormed`; out-of-range participant bit accesses are handled by total `freeAt`.

Safe wording:

> The heatmap is exactly the per-slot count of participant rows marked free, with out-of-range availability treated as not free.

### Best-Time Recommendation

For any event with `e.numSlots >= 0`:

- `isBest(e)` has one boolean per slot,
- a slot is marked exactly when its heatmap count equals `maxCount(heatmap(e))`,
- and the maximum is positive.

Safe wording:

> The best mask marks exactly all positive argmax slots and marks no slot when the maximum count is zero.

### Threshold Query

For any event with `e.numSlots >= 0` and any integer `k`:

- `availableAtLeast(e, k)[s] === (heatmap(e)[s] >= k)`

Note that `k <= 0` marks every slot because heatmap counts are non-negative.

### Well-Formedness And Replay

The implemented invariant is:

- `numSlots >= 0`
- every participant availability array has length `numSlots`

The following preserve that invariant under their stated preconditions:

- `initEvent`
- `addParticipant`
- `setAvailability`
- `removeParticipant`
- `applyOp`
- `replay`

Safe wording:

> Replay from a well-formed event preserves non-negative slot counts and correct availability-array lengths.

Unsafe wording:

> Replay preserves unique participant identity.

### Monotonicity

The proofs now support both:

- adding a well-formed participant row never lowers any slot count,
- replacing a matching participant's availability with a superset never lowers any slot count, under the stated subset precondition.

Safe wording:

> Counts are monotone under joins and under paints that only add availability for the targeted id.

### Participant-Order Independence

The proofs establish:

- concat homomorphism for `countFree`,
- batch commutativity,
- full participant-list permutation invariance for `countFree`,
- and heatmap permutation invariance.

Safe wording:

> The heatmap depends on the multiset of participant rows, not their order.

Unsafe wording:

> Arbitrary op arrival order does not matter.

The op-log claim is still stronger than the proof. Reordering a `paint` before its `join`, or changing the order of duplicate-id joins/paints, can change the final participant rows.

### LWW

The proof establishes:

- two `setAvailLWW` writes to the same `pid` commute when `t1 !== t2`.

Limitations:

- equal timestamps are not covered,
- join/paint interaction is not covered,
- whole-op replay permutation is not covered,
- uniqueness of the target participant id is not part of the main invariant.

### Export

The proofs now establish:

- sparse boolean-array round-trip,
- participant round-trip,
- participant-list round-trip under `allAvailLen(ps, n)`,
- event round-trip under `wellFormed(e)`,
- heatmap-over-export soundness,
- isBest-over-export soundness.

Safe wording:

> The in-memory sparse export model round-trips well-formed events, and `heatmap`/`isBest` are preserved after decode.

Unsafe wording:

> NDJSON export and all query endpoints are verified end to end.

### Queries

The proofs establish:

- `whoIsFree(e, s).length === heatmap(e)[s]`
- `freeParticipants` returns only free participants and includes every free participant value from the input list
- `participantsAt(e, s).length === heatmap(e)[s]`
- `overlap(e, pids)` exactly matches `allPidsFreeAt(e.participants, pids, s)`

Safe wording:

> The participant-list query used by `whoIsFree` is consistent with the heatmap count, and the overlap mask is correct relative to the implemented `allPidsFreeAt` predicate.

Unsafe wording:

> `participantsAt` is fully membership-exact and duplicate-free.

## Design-Doc Claim Matrix

| Design claim | Iteration 2 status |
|---|---|
| Heatmap is exactly the number of free participants per slot | Supported, where “participant” means row. |
| Recommendation flags exactly the best slots | Supported as a positive argmax mask. |
| No recommendation when nobody is available | Supported via `best > 0`. |
| Threshold query marks slots with at least `k` free | Supported. |
| Adding a participant never lowers counts | Supported. |
| Marking more slots never lowers counts | Supported under the explicit superset precondition. |
| Participant order does not affect heatmap | Supported, including full permutation invariance. |
| Op arrival order does not matter | Not supported for arbitrary op logs. |
| Same-participant LWW edits converge | Partially supported for two writes with distinct timestamps at the list-transform level. |
| Every reachable replay state is well-formed | Supported for A1+A3 only. |
| Participant ids are unique | Standalone preservation lemmas exist, but uniqueness is not part of `wellFormed` or replay preservation. |
| Export round-trips | Supported for the in-memory `SparseEvent` codec under `wellFormed`. Not NDJSON. |
| Queries over export equal live queries | Supported for `heatmap` and `isBest`; not yet for all queries. |
| `whoIsFree` count agrees with heatmap | Supported. |
| `whoIsFree` returns exactly free participants | Mostly supported at the `freeParticipants` helper level, by value membership. |
| `participantsAt` query | Implemented and count-consistent; membership-exact id semantics not proved. |
| `overlap` query | Implemented and proved relative to `allPidsFreeAt`; subset/person semantics depend on id uniqueness. |
| Grid slot index arithmetic verified in `src/grid.ts` | Not checkable in this workspace snapshot; no `quorum/src/grid.ts` exists. |
| Runtime checked by `npm test` | Not supported in this workspace snapshot; `package.json` still has the default failing test script. |
| Current VC count in design doc | Stale: local `domain.dfy` verification reports `142 verified, 0 errors`, not `90 verified, 0 errors`. |

## Notes On Proof Artifact Drift

`src/domain.dfy` differs substantially from `src/domain.dfy.gen`, as expected when manual Dafny proof bodies are maintained separately. One important detail from the diff: `domain.dfy.gen` still contains a generated `encodeEvent` body returning `Event(...)` where the final checked `domain.dfy` correctly returns `SparseEvent(...)`.

This means the guarantee checked above is specifically for `src/domain.dfy`. A future regeneration should be verified carefully to ensure it preserves the manual proof bodies and the `SparseEvent` correction.

## Remaining Gaps Before The Full Product Promise

1. Integrate A2 into the main invariant, for example `wellFormed(e) === A1 && A2 && A3`, or introduce a separate `strongWellFormed` and prove the replay/mutation story for it.

2. Make `applyOp(join)` uniqueness-aware, or explicitly state that duplicate ids are prevented by trusted shell/storage code outside the verified domain.

3. Prove query-over-export lemmas for `availableAtLeast`, `participantsAt`, and `overlap`.

4. Strengthen `participantsAt` with membership-exact id semantics, ideally under a unique-id invariant.

5. Decide and document `overlap([])` semantics. The current proof makes it true for every slot by vacuous truth; that may be mathematically clean but product-surprising.

6. Define the exact convergence theorem desired for ops. Current proofs support participant-row permutation invariance and two-write LWW commutativity, not arbitrary op-log permutation invariance.

7. If the product wants NDJSON/export trust, add an explicit serialization/parsing layer or state that byte-level export, endpoint routing, SQL, D1, and R2 remain trusted.

8. Align `DESIGN_QUORUM.md` with this workspace snapshot: no `grid.ts`, no app files, default failing `npm test`, stale proof count, and Stage 3 text that still says `participantsAt`/`overlap` are planned even though they now exist in `domain.ts`.

## Safest External Wording

Use this:

> Quorum's verified domain core proves that, for well-formed events, heatmaps are exact per-slot counts of free participant rows; best-time masks are exactly the positive argmax slots; threshold masks are exact heatmap comparisons; joins and availability-expanding paints cannot lower counts; participant-row order does not affect heatmaps; the implemented mutations and replay preserve the structural event invariant; same-id LWW writes with distinct timestamps commute; the in-memory sparse event codec round-trips; and `heatmap`/`isBest` are preserved over that codec.

Avoid this for now:

> The entire app, NDJSON export pipeline, storage/query endpoints, timezone mapping, unique participant identity, and arbitrary collaborative op convergence are verified end to end.
