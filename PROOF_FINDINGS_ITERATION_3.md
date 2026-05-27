# Quorum Domain Proof Review — Iteration 3

Reviewed:

- `src/domain.ts` (827 lines, annotated TypeScript)
- `src/domain.dfy.gen` (1072 lines, LemmaScript-generated Dafny)
- `src/domain.dfy` (1612 lines, working Dafny with hand-written proof bodies)
- `DESIGN_QUORUM.md` (the specification)
- prior review: `PROOF_FINDINGS_ITERATION_2.md`

Verification:

```
$ dafny verify src/domain.dfy
Dafny program verifier finished with 161 verified, 0 errors
```

No `//@ assume` or `//@ havoc` annotations found in `domain.ts`. No `assume` statements found in `domain.dfy`. All proof obligations are fully discharged.

---

## Executive Summary

This iteration completes every design-doc stage through 3b. The 161 verified VCs (up from 142 in iteration 2) close all major gaps identified in the prior review:

- **A2 (id uniqueness) is now integrated** via `wellFormedStrict` and proved to be preserved through the op model (`applyOpPreservesStrict`, `replayPreservesStrict`) under a `freshJoinIds` precondition.
- **`participantsAt` is now membership-exact** with `freeIdListMembership` (every returned id has a free source, every free participant's id is returned) and **duplicate-free** under `uniqueIds` via `freeIdListDistinct`.
- **Query-over-export is now proved for all four query families**: `heatmap`, `isBest`, `availableAtLeast`, and `overlap`.
- **Paint monotonicity** (`heatmapMonotoneUnderPaint` via `isSubsetOf`) was added in iteration 2 and remains verified.
- **Full permutation invariance** (`countFreePerm`/`heatmapPermInvariant`) now provides the strongest possible participant-order independence.

The safest high-level claim is:

> Quorum's verified domain core (161 VCs, 0 Dafny errors, no `assume`/`havoc` bypasses) proves: exact heatmap counting bounded by participant count; positive-argmax best masks with a zero guard; exact threshold masks; invariant preservation for all mutations and op-log replay (A1+A3 always, A1+A2+A3 under fresh join ids); monotonicity under joins and availability-expanding paints; full participant-permutation invariance of heatmaps; same-pid LWW commutativity for distinct timestamps; lossless in-memory sparse codec round-trip; query-over-export soundness for heatmap, isBest, availableAtLeast, and overlap; membership-exact and duplicate-free query results for participants-at under unique ids; and correct overlap masks.

What is **not** verified: NDJSON byte serialization, WebSocket/DO/D1/R2 I/O, timezone/calendar labeling, grid slot-index arithmetic (the design doc references `src/grid.ts` which is not present in this workspace), the React UI shell, and full op-log permutation invariance (only participant-list permutation and same-pid LWW are proved; reordering a join before its paint, or interleaving distinct-pid ops, is not covered by any convergence lemma).

---

## What Is Safely Guaranteed

### Aggregation (Family B) — Exact Heatmap, Best Mask, Threshold

The heatmap is the definitive count. For any event with `e.numSlots >= 0`:

- `heatmap(e)` has exactly `e.numSlots` entries (`heatmap_ensures`)
- Each entry equals `countFree(e.participants, s)` — the recursive count of participants whose `freeAt(p, s)` is true (`heatmap_ensures`)
- Each entry is bounded: `0 <= heatmap(e)[s] <= e.participants.length` (`heatmap_ensures`)
- `freeAt` is total: out-of-range slots are not free, in-range slots read the bitset (`freeAt_ensures`)

The best mask (`isBest`) marks exactly the slots whose count ties the maximum, with a zero guard:

- `isBest(e)[s] === (heatmap(e)[s] === maxCount(heatmap(e)) && maxCount(heatmap(e)) > 0)` (`isBest_ensures`)
- `maxCount` is precondition-free; it upper-bounds all entries and is attained by some entry when the list is non-empty (`maxCount_ensures`)

The threshold mask:

- `availableAtLeast(e, k)[s] === (heatmap(e)[s] >= k)` (`availableAtLeast_ensures`)

**Important**: These three results require only `e.numSlots >= 0`, not `wellFormed(e)`. The total `freeAt` makes the counting kernel work on any input.

### Well-Formedness (Family A) — Two Tiers of Invariant

**Tier 1 (`wellFormed`):** `e.numSlots >= 0` and every participant's `avail` has length `numSlots`. Preserved unconditionally by:

| Mutation | Lemma | Precondition |
|----------|-------|-------------|
| `initEvent` | `initEvent_ensures` | `numSlots >= 0` |
| `addParticipant` | `addParticipant_ensures` | `wellFormed(e)`, `p.avail.length === e.numSlots` |
| `setAvailability` | `setAvailability_ensures` | `wellFormed(e)`, `newAvail.length === e.numSlots` |
| `removeParticipant` | `removeParticipant_ensures` | `wellFormed(e)` |
| `applyOp` | `applyOpPreservesInv_ensures` | `wellFormed(e)` |
| `replay` | `replayPreservesInv_ensures` | `wellFormed(e)` |

**Tier 2 (`wellFormedStrict`):** `wellFormed(e) && uniqueIds(e.participants)` — adds A2 (participant id uniqueness). Preserved through the op model when join ops introduce fresh ids:

- `initEventStrict_ensures`: a fresh event is strictly well-formed
- `applyOpPreservesStrict_ensures`: requires `wellFormedStrict(e)` and, for joins, `!idTaken(e.participants, op.participant.id)`
- `replayPreservesStrict_ensures`: requires `wellFormedStrict(e)` and `freshJoinIds(e, ops)`

The `freshJoinIds` predicate is a dynamic check over the op log: each join op's participant id must not already be taken at the point it is applied. This is the formal justification for the design doc's claim that "every reachable state via the op model has unique participant ids" — provided the trusted shell ensures fresh ids for join operations.

Standalone uniqueness-preservation lemmas exist for each list transform: `uniqueIdsPreservedByJoin`, `uniqueIdsPreservedBySetAvail`, `uniqueIdsPreservedByRemove`, `uniqueIdsPreservedByLWW`.

### Monotonicity (Family C) — Joins and Paints

Two forms are proved:

**C1 — Join monotonicity:** Adding a well-formed participant never lowers any slot's count:

```
heatmap(addParticipant(e, p))[s] >= heatmap(e)[s]
```

Proved via the `countFreeConcat` homomorphism plus non-negativity of `countFree([p], s)` (`heatmapMonotoneUnderJoin_ensures`).

**C2 — Paint monotonicity:** Replacing a participant's availability with a superset (more slots marked free) never lowers any slot's count:

```
forall(i, ... e.participants[i].id === pid ==> isSubsetOf(e.participants[i].avail, newAvail))
==> heatmap(setAvailability(e, pid, newAvail))[s] >= heatmap(e)[s]
```

Proved via `freeAtMonotone`, `countFreeMonotoneSetAvail`, and `heatmapMonotoneUnderPaint`. The `isSubsetOf` precondition is quantified over all matching participants — under unique ids (the normal case), there is at most one.

**Unanimity:** If every participant is free at slot `s` and there is at least one participant, then `isBest(e)[s] === true` (`unanimousIsBest_ensures`).

### Convergence (Family D) — Permutation Invariance and LWW

**D1 — Full permutation invariance.** The strongest convergence result: two events whose participant lists are permutations of each other (same multiset) have identical heatmaps:

```
perm(a.participants, b.participants) ==> heatmap(a)[s] === heatmap(b)[s]
```

Proved via `countFreePerm_ensures` (remove-one-element induction using `countFreeRemoveAt` and `countFreeConcat`) and lifted to `heatmapPermInvariant_ensures`. The `perm(...)` predicate lowers to Dafny's `multiset(a) == multiset(b)`.

This subsumes the weaker batch results (`countFreeConcat`, `countFreeComm`, `heatmapBatchOrderInvariant`), which remain in the codebase and serve as stepping stones.

**D2 — Same-pid LWW commutativity.** Two LWW writes to the same participant id with distinct timestamps commute:

```
t1 !== t2 ==>
  setAvailLWW(setAvailLWW(ps, pid, a1, t1), pid, a2, t2)
  === setAvailLWW(setAvailLWW(ps, pid, a2, t2), pid, a1, t1)
```

Proved by `setAvailLWWCommutes_ensures`. Limitations: equal timestamps are not covered (the precondition requires `t1 != t2`); cross-pid interaction is not modeled; join/paint ordering is not covered.

**Op model.** `applyOp` is total — bad avail lengths are no-ops. `replay` folds an op log. Both preserve `wellFormed` unconditionally and `wellFormedStrict` under `freshJoinIds`.

### Export Faithfulness (Family E) — Codec Round-Trip and Query Soundness

**E1 — Sparse round-trip.** The dense-to-sparse-to-dense codec is the identity:

- Per boolean array: `densify(sparsify(a), a.length)[i] === a[i]` for all in-range `i` (`sparseRoundTrip_ensures`)
- Per participant: `decodeParticipant(encodeParticipant(p), p.avail.length) === p` (`participantRoundTrip_ensures`)
- Per participant list: `decodeParticipants(encodeParticipants(ps), n) === ps` under `allAvailLen(ps, n)` (`participantsListRoundTrip_ensures`)
- Per event: `decodeEvent(encodeEvent(e)) === e` under `wellFormed(e)` (`eventRoundTrip_ensures`)

The codec is characterized through `contains` (set membership), not sortedness.

**E2 — Query-over-export soundness.** For a well-formed event, encoding and decoding preserves the output of all four query families:

| Query | Lemma | What it proves |
|-------|-------|---------------|
| `heatmap` | `heatmapOverExport_ensures` | Pointwise heatmap equality |
| `isBest` | `isBestOverExport_ensures` | Pointwise best-mask equality |
| `availableAtLeast` | `availableAtLeastOverExport_ensures` | Pointwise threshold-mask equality |
| `overlap` | `overlapOverExport_ensures` | Pointwise overlap-mask equality |

These are technically corollaries of `eventRoundTrip` (since `decodeEvent(encodeEvent(e)) === e` and all queries are pure), but the explicit lemmas make the proof obligation checkable by Dafny without chaining.

**Scope limitation:** The round-trip proof is for in-memory `SparseEvent` values. It does not cover NDJSON byte serialization, parse errors, schema evolution, streaming format, SQL tables, D1, or R2. These remain trusted.

### Query Algebra (Family F) — Membership-Exact, Duplicate-Free

**`whoIsFree` / `freeParticipants`:**

- Count-consistent: `whoIsFree(e, s).length === heatmap(e)[s]` (`whoIsFree_ensures`)
- Membership-exact: every returned participant is free at `s`, and every free participant from the input is in the result (`freeParticipantsMembership_ensures`)

**`participantsAt` / `freeIdList`:**

- Count-consistent: `participantsAt(e, s).length === heatmap(e)[s]` (`participantsAt_ensures`)
- Membership-exact: every returned id has a corresponding free participant in the input, and every free participant's id appears in the result (`freeIdListMembership_ensures`)
- Duplicate-free under `uniqueIds`: `noDupStrings(freeIdList(ps, s))` when `uniqueIds(ps)` (`freeIdListDistinct_ensures`)

**`overlap`:**

- `overlap(e, pids)[s] === allPidsFreeAt(e.participants, pids, s)` (`overlap_ensures`)
- `allPidsFreeAt` checks that every requested pid has some row in the participant list that is free at `s` (via `pidFreeAt`)
- For empty `pids`, `allPidsFreeAt` returns `true` for every slot (vacuous truth — mathematically clean, potentially product-surprising)

---

## Design-Doc Claims: Status Table

Claims from DESIGN_QUORUM.md §2 (the promise) and §7 (properties):

| # | Design-doc claim | Status | Notes |
|---|-----------------|--------|-------|
| 1 | The heatmap is the count — each slot's number is exactly the number of free participants, never off by one, never double-counting | **Supported** | `heatmap_ensures`: pointwise `countFree`, bounded by participant count |
| 2 | The recommendation flags exactly the best slots | **Supported** | `isBest_ensures`: positive-argmax mask with `best > 0` guard |
| 3 | No recommendation when nobody is available | **Supported** | `maxCount(heatmap(e)) > 0` guard in `isBest` |
| 4 | Adding a participant or marking more slots never lowers any slot's count (monotonicity) | **Supported** | `heatmapMonotoneUnderJoin_ensures` for joins; `heatmapMonotoneUnderPaint_ensures` for availability-expanding paints under `isSubsetOf` |
| 5 | Participant order does not affect heatmap (convergence) | **Supported** | `heatmapPermInvariant_ensures`: full multiset permutation invariance |
| 6 | Because each participant owns only their own row, the heatmap is independent of the order edits arrive in | **Supported for participant rows** | Permutation invariance is proved. Op-log arrival order invariance is not fully proved (see Main Gaps #1) |
| 7 | Export round-trips, and queries over it are sound | **Supported at model level** | `eventRoundTrip_ensures` + explicit query-over-export for `heatmap`, `isBest`, `availableAtLeast`, `overlap` |
| 8 | Every mutation preserves `Inv` (A1+A3) | **Supported** | All 6 mutations + `applyOp` + `replay` |
| 9 | Strict invariant (A1+A2+A3) preserved through ops/replay | **Supported** | `applyOpPreservesStrict_ensures` + `replayPreservesStrict_ensures` under `freshJoinIds` |
| 10 | Same-participant LWW writes with distinct timestamps converge | **Supported** | `setAvailLWWCommutes_ensures` |
| 11 | `availableAtLeast` is an exact threshold mask | **Supported** | `availableAtLeast_ensures` |
| 12 | `whoIsFree` count agrees with heatmap; membership-exact | **Supported** | `whoIsFree_ensures` + `freeParticipantsMembership_ensures` |
| 13 | `participantsAt`: membership-exact + distinct under `uniqueIds` | **Supported** | `freeIdListMembership_ensures` + `freeIdListDistinct_ensures` |
| 14 | `overlap` returns correct mask per `allPidsFreeAt` | **Supported** | `overlap_ensures` |
| 15 | Sparse codec `densify(sparsify(a)) === a` | **Supported** | `sparseRoundTrip_ensures` |
| 16 | Event-level `decodeEvent(encodeEvent(e)) === e` | **Supported** | `eventRoundTrip_ensures` under `wellFormed(e)` |
| 17 | D1 full-permutation invariance via `perm(...)` | **Supported** | `countFreePerm_ensures` + `heatmapPermInvariant_ensures` |
| 18 | Grid slot-index arithmetic verified in `src/grid.ts` | **Not checkable** | No `grid.ts` in this workspace snapshot |
| 19 | Runtime-checked by `npm test` (`test/smoke.mjs`) | **Not checkable** | `package.json` has default failing test script; no `test/` directory |
| 20 | 161 VCs, 0 errors (design doc header) | **Supported** | `dafny verify src/domain.dfy` returns exactly `161 verified, 0 errors` |
| 21 | E3 (append-only integrity via D1 PRIMARY KEY) | **Trusted mechanism** | DB-enforced, not in verified code — correctly stated as trusted in design doc |
| 22 | E4 (canonical encoding — same event, same bytes) | **Partially supported** | `encodeEvent` is a pure function (deterministic). Byte-level determinism depends on NDJSON serializer |

---

## Main Gaps

1. **Op-log permutation invariance is partial.** The proofs establish participant-list permutation invariance (Family D1) and same-pid LWW commutativity (Family D2). But there is no lemma showing that two different orderings of an op log produce the same final event state. Reordering a `paint` before its corresponding `join` changes behavior (the paint becomes a no-op on a missing row). The design doc is careful — §2.4 says "the heatmap is independent of the order edits arrive in" and the proofs support this at the participant-row level. But the casual reader might infer arbitrary op-log convergence. To close this gap, one would need to prove that for op logs where all joins precede their paints and the same multiset of final participant rows is reached, the heatmap is identical. The single-threaded Durable Object in practice serializes all ops, making this a pragmatic non-issue.

2. **`grid.ts` is absent from this workspace.** The design doc (§2) claims cell-to-slot index arithmetic is verified in `src/grid.ts` with in-range + injective properties. No such file exists in `quorum/src/`. Either it lives in the app source directory outside `quorum/`, was removed, or has not yet been written.

3. **`npm test` is not operational.** The design doc references `test/smoke.mjs` as a runtime check. The workspace has no test directory and `package.json` has the default `echo "Error: no test specified" && exit 1`.

4. **NDJSON / byte-level export.** The export proof covers the in-memory `SparseEvent` codec. JSON serialization fidelity, field ordering, streaming behavior, and R2 storage integrity are all trusted. The design doc is honest about this (§6 trust boundary).

5. **`overlap` with empty `pids`.** `allPidsFreeAt(ps, [], s)` returns `true` for every slot by vacuous truth. Mathematically correct but potentially product-surprising. Consider documenting this edge case.

6. **Equal-timestamp LWW.** `setAvailLWWCommutes` requires `t1 !== t2`. Two writes at the same timestamp do not commute in general. The design doc acknowledges this (§11) and the single-threaded Durable Object prevents equal timestamps in practice.

---

## Proof Artifact Notes

### `.dfy.gen` vs `.dfy` Divergence

`domain.dfy.gen` (raw LemmaScript output) and `domain.dfy` (verified file with proof bodies) diverge in a known way:

- `encodeEvent` in `.dfy.gen` (line 889) returns `Event(...)` — wrong constructor. The `.dfy` (line 1314) correctly returns `SparseEvent(...)`. This is a LemmaScript codegen issue where the result type constructor matches the wrong datatype.
- The `.dfy` adds ~540 lines of proof bodies (helper lemmas, inductive steps, `forall...ensures` blocks) absent from `.dfy.gen`.
- The `.dfy` adds an `ensures` clause to `heatmapUpto` (line 96: `ensures |heatmapUpto(ps, k)| == k`) needed as a function postcondition for callers that need the length fact in function bodies, not just in lemmas.

All proofs are checked against `domain.dfy`, not `.dfy.gen`. A future `lsc regen` must preserve the `SparseEvent` correction and all proof bodies. The design doc (§10) documents the `regen` + `.dfy.base` gotcha.

### No Proof Bypasses

- Zero `//@ assume` annotations in `domain.ts`
- Zero `assume` statements in `domain.dfy`
- Zero `//@ havoc` annotations in `domain.ts`

All 161 verification conditions are fully discharged by Dafny.

---

## Changes Since Iteration 2

| Gap from iteration 2 | Status in iteration 3 |
|---|---|
| A2 not in `wellFormed` or replay | **Closed.** `wellFormedStrict` = A1+A2+A3; `applyOpPreservesStrict`/`replayPreservesStrict` under `freshJoinIds` |
| `applyOp(join)` can introduce duplicate ids | **Addressed.** `applyOpPreservesStrict` requires `!idTaken` for joins. Direct `addParticipant` still preserves only `wellFormed`, not `wellFormedStrict`, but the op-model path is the intended usage |
| `participantsAt` only count-proved | **Closed.** `freeIdListMembership` proves membership-exactness; `freeIdListDistinct` proves duplicate-freedom under `uniqueIds` |
| Query-over-export missing for `availableAtLeast`/`overlap` | **Closed.** Explicit lemmas added for both. `participantsAt`/`whoIsFree` over export follow trivially from `eventRoundTrip` |
| VC count stale in design doc | **Closed.** Design doc says 161; verification produces 161 |

---

## Safe External Wording

**Use this:**

> Quorum's domain core is verified by 161 Dafny proof obligations with zero errors and no proof bypasses. The proofs establish: per-slot heatmap counts are exactly the number of free participant rows, bounded by the participant total; the best-time mask flags exactly the positive-argmax slots; threshold masks are exact; the well-formedness invariant (correct array lengths, non-negative slot count) is preserved by all mutations and op-log replay; the strict invariant (adding unique participant ids) is preserved through the op model when join ids are fresh; joins and availability-expanding paints cannot lower any slot's count; the heatmap depends only on the multiset of participant rows, not their order; same-participant last-writer-wins updates with distinct timestamps commute; the in-memory sparse export codec round-trips well-formed events exactly; heatmap, best-mask, threshold, and overlap queries produce the same output over the decoded export as over the live event; and the "who is free" and "participants at" queries are membership-exact and duplicate-free under unique ids.

**Do not claim yet:**

- "The entire app is verified end to end" — the React UI, WebSocket I/O, Durable Object, D1/R2 storage, and timezone labeling are trusted shell.
- "Arbitrary op-log reordering converges" — only participant-row permutation and same-pid LWW (distinct timestamps) are proved; join-before-paint ordering matters.
- "The NDJSON export is verified" — the proof is for the in-memory codec model, not byte serialization.
- "Grid slot-index arithmetic is verified" — no `grid.ts` exists in this workspace to check.
- "The test suite validates runtime behavior" — no operational test suite is present.
