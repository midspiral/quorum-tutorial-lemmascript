//@ backend dafny

// ═══════════════════════════════════════════════════════════════
// Quorum — verified domain core
//
// A when2meet clone: participants paint availability on a grid of
// abstract slot indices [0, numSlots). The verified core guarantees
// the heatmap, best-time recommendation, convergence, and export
// are correct.
//
// Style: pure recursive functions, a TOTAL counting kernel
// (freeAt/countFree carry no precondition), and each //@ ensures
// discharged by an inductive proof in the companion .dfy.
// ═══════════════════════════════════════════════════════════════

// ── Types ─────────────────────────────────────────────────────

interface Participant {
  id: string
  name: string
  avail: boolean[]
  updatedAt: number
}

interface Event {
  id: string
  title: string
  numSlots: number
  participants: Participant[]
}

export type { Participant, Event }

// ── Counting kernel ───────────────────────────────────────────

// Is participant `p` free at slot `s`? — TOTAL: out-of-range slots
// are not free. (The foundation the entire aggregation rests on.)
export function freeAt(p: Participant, s: number): boolean {
  //@ verify
  //@ ensures (0 <= s && s < p.avail.length) ==> \result === p.avail[s]
  //@ ensures !(0 <= s && s < p.avail.length) ==> \result === false
  if (s < 0 || s >= p.avail.length) return false
  return p.avail[s]
}

// The number of participants free at slot `s`. Precondition-free
// recursive count; the spec-level count and the engine that
// produces it are the same function.
export function countFree(ps: Participant[], s: number): number {
  //@ verify
  //@ decreases ps.length
  //@ ensures 0 <= \result && \result <= ps.length
  if (ps.length === 0) return 0
  const rest = countFree(ps.slice(1), s)
  return (freeAt(ps[0], s) ? 1 : 0) + rest
}

// ── Well-formedness (Family A) ────────────────────────────────

// A1: every participant's bitset matches the grid. Recursive
// predicate carrying a reflection lemma: when it returns true,
// the quantified per-element fact is available to callers.
export function allAvailLen(ps: Participant[], n: number): boolean {
  //@ verify
  //@ decreases ps.length
  //@ ensures \result === true ==> forall(i, 0 <= i && i < ps.length ==> ps[i].avail.length === n)
  if (ps.length === 0) return true
  if (ps[0].avail.length !== n) return false
  return allAvailLen(ps.slice(1), n)
}

// Completeness of the reflection: the quantified bound rebuilds
// the predicate. (Pure-carrier lemma; induction in the .dfy.)
export function allAvailLenComplete(ps: Participant[], n: number): boolean {
  //@ verify
  //@ requires forall(i, 0 <= i && i < ps.length ==> ps[i].avail.length === n)
  //@ decreases ps.length
  //@ ensures allAvailLen(ps, n) === true
  return true
}

// Inv(e) = A3 ∧ A1: numSlots is non-negative and every
// participant's avail has the right length.
export function wellFormed(e: Event): boolean {
  //@ verify
  return e.numSlots >= 0 && allAvailLen(e.participants, e.numSlots)
}

// ── Aggregation (Family B) ────────────────────────────────────

// Build the heatmap for the first `k` slots. Recurses on `k`
// (not by slicing participants) so slot indices stay absolute.
export function heatmapUpto(ps: Participant[], k: number): number[] {
  //@ verify
  //@ requires 0 <= k
  //@ decreases k
  //@ ensures \result.length === k
  //@ ensures forall(s, 0 <= s && s < k ==> \result[s] === countFree(ps, s))
  if (k === 0) return []
  return [...heatmapUpto(ps, k - 1), countFree(ps, k - 1)]
}

// The heatmap: per-slot count of free participants.
export function heatmap(e: Event): number[] {
  //@ verify
  //@ requires e.numSlots >= 0
  //@ ensures \result.length === e.numSlots
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> \result[s] === countFree(e.participants, s))
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> 0 <= \result[s] && \result[s] <= e.participants.length)
  return heatmapUpto(e.participants, e.numSlots)
}

// Maximum entry in a number[]. Precondition-free so it composes
// inside isBest. NOT floored at 0: the max of a non-empty list
// is an actual element (so maxCount([-5]) === -5, not 0).
export function maxCount(h: number[]): number {
  //@ verify
  //@ decreases h.length
  //@ ensures forall(s, 0 <= s && s < h.length ==> h[s] <= \result)
  //@ ensures h.length > 0 ==> exists(s, 0 <= s && s < h.length && h[s] === \result)
  if (h.length === 0) return 0
  if (h.length === 1) return h[0]
  const rest = maxCount(h.slice(1))
  return h[0] >= rest ? h[0] : rest
}

// Build the best-slot mask for the first `k` slots.
export function isBestUpto(h: number[], best: number, k: number): boolean[] {
  //@ verify
  //@ requires 0 <= k && k <= h.length
  //@ decreases k
  //@ ensures \result.length === k
  //@ ensures forall(s, 0 <= s && s < k ==> \result[s] === (h[s] === best && best > 0))
  if (k === 0) return []
  return [...isBestUpto(h, best, k - 1), h[k - 1] === best && best > 0]
}

// "Best" as a boolean MASK over slots: slot s is best iff its
// count ties the max AND the max is positive (B5 — no
// recommendation when nobody has entered anything).
export function isBest(e: Event): boolean[] {
  //@ verify
  //@ requires e.numSlots >= 0
  //@ ensures heatmap(e).length === e.numSlots
  //@ ensures \result.length === e.numSlots
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> \result[s] === (heatmap(e)[s] === maxCount(heatmap(e)) && maxCount(heatmap(e)) > 0))
  const h = heatmap(e)
  const best = maxCount(h)
  return isBestUpto(h, best, e.numSlots)
}

// Build the threshold mask for the first `k` slots.
export function availableAtLeastUpto(h: number[], k: number, threshold: number): boolean[] {
  //@ verify
  //@ requires 0 <= k && k <= h.length
  //@ decreases k
  //@ ensures \result.length === k
  //@ ensures forall(s, 0 <= s && s < k ==> \result[s] === (h[s] >= threshold))
  if (k === 0) return []
  return [...availableAtLeastUpto(h, k - 1, threshold), h[k - 1] >= threshold]
}

// Threshold query: boolean mask of slots where at least `k`
// participants are free.
export function availableAtLeast(e: Event, k: number): boolean[] {
  //@ verify
  //@ requires e.numSlots >= 0
  //@ ensures heatmap(e).length === e.numSlots
  //@ ensures \result.length === e.numSlots
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> \result[s] === (heatmap(e)[s] >= k))
  const h = heatmap(e)
  return availableAtLeastUpto(h, e.numSlots, k)
}

// ── Mutation helpers ──────────────────────────────────────────

export function idTaken(ps: Participant[], pid: string): boolean {
  //@ verify
  //@ decreases ps.length
  if (ps.length === 0) return false
  if (ps[0].id === pid) return true
  return idTaken(ps.slice(1), pid)
}

export function setAvailInList(ps: Participant[], pid: string, newAvail: boolean[]): Participant[] {
  //@ verify
  //@ decreases ps.length
  //@ ensures \result.length === ps.length
  if (ps.length === 0) return []
  if (ps[0].id === pid) return [{ ...ps[0], avail: newAvail }, ...ps.slice(1)]
  return [ps[0], ...setAvailInList(ps.slice(1), pid, newAvail)]
}

export function removeFromList(ps: Participant[], pid: string): Participant[] {
  //@ verify
  //@ decreases ps.length
  if (ps.length === 0) return []
  if (ps[0].id === pid) return ps.slice(1)
  return [ps[0], ...removeFromList(ps.slice(1), pid)]
}

// ── Mutations (Stage 0b) ─────────────────────────────────────

export function initEvent(id: string, title: string, numSlots: number): Event {
  //@ verify
  //@ requires numSlots >= 0
  //@ ensures wellFormed(\result)
  //@ ensures \result.numSlots === numSlots
  //@ ensures \result.participants.length === 0
  return { id: id, title: title, numSlots: numSlots, participants: [] }
}

export function addParticipant(e: Event, p: Participant): Event {
  //@ verify
  //@ requires wellFormed(e) && p.avail.length === e.numSlots
  //@ ensures wellFormed(\result)
  //@ ensures \result.numSlots === e.numSlots
  return { ...e, participants: [...e.participants, p] }
}

export function setAvailability(e: Event, pid: string, newAvail: boolean[]): Event {
  //@ verify
  //@ requires wellFormed(e) && newAvail.length === e.numSlots
  //@ ensures wellFormed(\result)
  //@ ensures \result.numSlots === e.numSlots
  return { ...e, participants: setAvailInList(e.participants, pid, newAvail) }
}

export function removeParticipant(e: Event, pid: string): Event {
  //@ verify
  //@ requires wellFormed(e)
  //@ ensures wellFormed(\result)
  //@ ensures \result.numSlots === e.numSlots
  return { ...e, participants: removeFromList(e.participants, pid) }
}

// ── Monotonicity (Family C) ──────────────────────────────────

// C1: a join never lowers any slot's count. Proof: countFree
// homomorphism + non-negativity.
export function heatmapMonotoneUnderJoin(e: Event, p: Participant): boolean {
  //@ verify
  //@ requires wellFormed(e) && p.avail.length === e.numSlots
  //@ ensures heatmap(addParticipant(e, p)).length === e.numSlots
  //@ ensures heatmap(e).length === e.numSlots
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> heatmap(addParticipant(e, p))[s] >= heatmap(e)[s])
  return true
}

// C2: if everyone is free at s, then s is a best slot.
export function unanimousIsBest(e: Event, s: number): boolean {
  //@ verify
  //@ requires e.numSlots >= 0 && e.participants.length > 0 && 0 <= s && s < e.numSlots
  //@ requires forall(i, 0 <= i && i < e.participants.length ==> freeAt(e.participants[i], s) === true)
  //@ ensures isBest(e).length === e.numSlots
  //@ ensures isBest(e)[s] === true
  return true
}

// ── Convergence core (Family D) ──────────────────────────────

// Homomorphism: counting two batches and adding === counting
// the joined list. Factors countFree through (ℤ, +).
export function countFreeConcat(xs: Participant[], ys: Participant[], s: number): boolean {
  //@ verify
  //@ ensures countFree(xs.concat(ys), s) === countFree(xs, s) + countFree(ys, s)
  return true
}

// Batch commutativity (corollary of the homomorphism + ℤ commutativity).
export function countFreeComm(xs: Participant[], ys: Participant[], s: number): boolean {
  //@ verify
  //@ ensures countFree(xs.concat(ys), s) === countFree(ys.concat(xs), s)
  return true
}

// Lifted to the observable: two events differing only by the
// order of two participant batches have identical heatmaps.
export function heatmapBatchOrderInvariant(a: Event, b: Event, xs: Participant[], ys: Participant[]): boolean {
  //@ verify
  //@ requires a.numSlots >= 0 && a.numSlots === b.numSlots
  //@ requires a.participants === xs.concat(ys) && b.participants === ys.concat(xs)
  //@ ensures heatmap(a).length === a.numSlots
  //@ ensures heatmap(b).length === b.numSlots
  //@ ensures forall(s, 0 <= s && s < a.numSlots ==> heatmap(a)[s] === heatmap(b)[s])
  return true
}

// ── LWW (Family D2) ──────────────────────────────────────────

// Last-writer-wins update: write a participant's avail only if
// the incoming timestamp is strictly newer.
export function setAvailLWW(ps: Participant[], pid: string, avail: boolean[], ts: number): Participant[] {
  //@ verify
  //@ decreases ps.length
  //@ ensures \result.length === ps.length
  if (ps.length === 0) return []
  if (ps[0].id === pid) {
    if (ts > ps[0].updatedAt) {
      return [{ ...ps[0], avail: avail, updatedAt: ts }, ...ps.slice(1)]
    }
    return ps
  }
  return [ps[0], ...setAvailLWW(ps.slice(1), pid, avail, ts)]
}

// D2: concurrent LWW writes with distinct timestamps commute.
export function setAvailLWWCommutes(
  ps: Participant[], pid: string,
  a1: boolean[], t1: number,
  a2: boolean[], t2: number
): boolean {
  //@ verify
  //@ requires t1 !== t2
  //@ ensures setAvailLWW(setAvailLWW(ps, pid, a1, t1), pid, a2, t2) === setAvailLWW(setAvailLWW(ps, pid, a2, t2), pid, a1, t1)
  return true
}

// ── Op model + replay (Stage 2b) ─────────────────────────────

type Op =
  | { kind: "join"; participant: Participant }
  | { kind: "paint"; pid: string; avail: boolean[]; ts: number }

export type { Op }

// applyOp is TOTAL — a bad avail length is a no-op, so it
// composes inside replay with no precondition.
export function applyOp(e: Event, op: Op): Event {
  //@ verify
  //@ ensures \result.numSlots === e.numSlots
  if (op.kind === "join") {
    if (op.participant.avail.length !== e.numSlots) return e
    return { ...e, participants: [...e.participants, op.participant] }
  }
  if (op.avail.length !== e.numSlots) return e
  return { ...e, participants: setAvailLWW(e.participants, op.pid, op.avail, op.ts) }
}

// Every op preserves the invariant.
export function applyOpPreservesInv(e: Event, op: Op): boolean {
  //@ verify
  //@ requires wellFormed(e)
  //@ ensures wellFormed(applyOp(e, op))
  return true
}

// replay folds a totally-ordered op log over an initial event.
export function replay(e: Event, ops: Op[]): Event {
  //@ verify
  //@ decreases ops.length
  if (ops.length === 0) return e
  return replay(applyOp(e, ops[0]), ops.slice(1))
}

// Every reachable state from a well-formed event stays well-formed.
export function replayPreservesInv(e: Event, ops: Op[]): boolean {
  //@ verify
  //@ requires wellFormed(e)
  //@ decreases ops.length
  //@ ensures wellFormed(replay(e, ops))
  return true
}

// ── Convergence deep (Family D1) ─────────────────────────────

// Full element-level permutation invariance of the count.
// perm(xs, ys) lowers to Dafny's multiset(a) == multiset(b).
export function countFreePerm(xs: Participant[], ys: Participant[], s: number): boolean {
  //@ verify
  //@ requires perm(xs, ys)
  //@ ensures countFree(xs, s) === countFree(ys, s)
  return true
}

// Lifted to the observable: two events whose participant lists
// are permutations of each other have identical heatmaps.
export function heatmapPermInvariant(a: Event, b: Event): boolean {
  //@ verify
  //@ requires a.numSlots >= 0 && a.numSlots === b.numSlots
  //@ requires perm(a.participants, b.participants)
  //@ ensures heatmap(a).length === a.numSlots
  //@ ensures heatmap(b).length === b.numSlots
  //@ ensures forall(s, 0 <= s && s < a.numSlots ==> heatmap(a)[s] === heatmap(b)[s])
  return true
}

// ── Codec (Family E) ─────────────────────────────────────────

// Membership predicate for a number array (spec-level).
export function contains(arr: number[], x: number): boolean {
  //@ verify
  //@ decreases arr.length
  if (arr.length === 0) return false
  if (arr[0] === x) return true
  return contains(arr.slice(1), x)
}

// Collect indices where a[i] is true, starting from position k.
export function sparsifyFrom(a: boolean[], k: number): number[] {
  //@ verify
  //@ requires 0 <= k
  //@ decreases a.length - k
  //@ ensures forall(i, contains(\result, i) === (k <= i && i < a.length && a[i]))
  if (k >= a.length) return []
  const rest = sparsifyFrom(a, k + 1)
  return a[k] ? [k, ...rest] : rest
}

// Sparse encoding: the sorted list of true-bit indices.
// Characterized through membership (contains), not sortedness.
export function sparsify(a: boolean[]): number[] {
  //@ verify
  //@ ensures forall(i, contains(\result, i) === (0 <= i && i < a.length && a[i]))
  return sparsifyFrom(a, 0)
}

// Build a boolean array from a sparse index list, first k slots.
export function densifyUpto(idxs: number[], k: number): boolean[] {
  //@ verify
  //@ requires 0 <= k
  //@ decreases k
  //@ ensures \result.length === k
  //@ ensures forall(i, 0 <= i && i < k ==> \result[i] === contains(idxs, i))
  if (k === 0) return []
  return [...densifyUpto(idxs, k - 1), contains(idxs, k - 1)]
}

// Decode a sparse index list back to a dense bitset.
export function densify(idxs: number[], n: number): boolean[] {
  //@ verify
  //@ requires 0 <= n
  //@ ensures \result.length === n
  //@ ensures forall(i, 0 <= i && i < n ==> \result[i] === contains(idxs, i))
  return densifyUpto(idxs, n)
}

// E1 round-trip: densify ∘ sparsify is the identity on a bitset.
export function sparseRoundTrip(a: boolean[]): boolean {
  //@ verify
  //@ ensures densify(sparsify(a), a.length).length === a.length
  //@ ensures forall(i, 0 <= i && i < a.length ==> densify(sparsify(a), a.length)[i] === a[i])
  return true
}

// ── Queries (Family F) ───────────────────────────────────────

// The participants free at slot `s`, by construction the
// freeAt-filter of the roster. Its length provably equals the
// heatmap count, so a tooltip can never disagree with the cell.
export function freeParticipants(ps: Participant[], s: number): Participant[] {
  //@ verify
  //@ decreases ps.length
  //@ ensures \result.length === countFree(ps, s)
  if (ps.length === 0) return []
  const rest = freeParticipants(ps.slice(1), s)
  return freeAt(ps[0], s) ? [ps[0], ...rest] : rest
}

// Who is free at slot s? Length provably equals heatmap(e)[s].
export function whoIsFree(e: Event, s: number): Participant[] {
  //@ verify
  //@ requires e.numSlots >= 0 && 0 <= s && s < e.numSlots
  //@ ensures heatmap(e).length === e.numSlots
  //@ ensures \result.length === heatmap(e)[s]
  return freeParticipants(e.participants, s)
}

// ── Record-update helper (for use in annotations) ─────────────

export function withAvail(p: Participant, a: boolean[]): Participant {
  //@ verify
  return { ...p, avail: a }
}

// ── Availability subset (total, for paint monotonicity) ───────

export function isSubsetOf(a: boolean[], b: boolean[]): boolean {
  //@ verify
  //@ decreases a.length
  //@ ensures \result === true ==> a.length === b.length
  //@ ensures a.length === b.length && \result === true ==> forall(i, 0 <= i && i < a.length && a[i] === true ==> b[i] === true)
  if (a.length !== b.length) return false
  if (a.length === 0) return true
  if (a[0] && !b[0]) return false
  return isSubsetOf(a.slice(1), b.slice(1))
}

// ── Paint monotonicity (Family C strengthening) ──────────────

// freeAt is monotone in avail: a superset preserves freedom
export function freeAtMonotone(p: Participant, newAvail: boolean[], s: number): boolean {
  //@ verify
  //@ requires p.avail.length === newAvail.length
  //@ requires forall(i, 0 <= i && i < p.avail.length && p.avail[i] === true ==> newAvail[i] === true)
  //@ ensures freeAt(p, s) === true ==> freeAt(withAvail(p, newAvail), s) === true
  return true
}

// countFree doesn't decrease when one participant's avail grows
export function countFreeMonotoneSetAvail(ps: Participant[], pid: string, newAvail: boolean[], s: number): boolean {
  //@ verify
  //@ decreases ps.length
  //@ requires forall(i, 0 <= i && i < ps.length && ps[i].id === pid ==> isSubsetOf(ps[i].avail, newAvail) === true)
  //@ ensures countFree(setAvailInList(ps, pid, newAvail), s) >= countFree(ps, s)
  return true
}

// Heatmap doesn't decrease when painting more availability
export function heatmapMonotoneUnderPaint(e: Event, pid: string, newAvail: boolean[]): boolean {
  //@ verify
  //@ requires wellFormed(e) && newAvail.length === e.numSlots
  //@ requires forall(i, 0 <= i && i < e.participants.length && e.participants[i].id === pid ==> isSubsetOf(e.participants[i].avail, newAvail) === true)
  //@ ensures heatmap(setAvailability(e, pid, newAvail)).length === e.numSlots
  //@ ensures heatmap(e).length === e.numSlots
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> heatmap(setAvailability(e, pid, newAvail))[s] >= heatmap(e)[s])
  return true
}

// ── Id uniqueness (Family A2) ─────────────────────────────────

export function uniqueIds(ps: Participant[]): boolean {
  //@ verify
  //@ decreases ps.length
  if (ps.length === 0) return true
  if (idTaken(ps.slice(1), ps[0].id)) return false
  return uniqueIds(ps.slice(1))
}

export function uniqueIdsPreservedByJoin(ps: Participant[], p: Participant): boolean {
  //@ verify
  //@ requires uniqueIds(ps) && !idTaken(ps, p.id)
  //@ ensures uniqueIds(ps.concat([p]))
  return true
}

export function idTakenSetAvail(ps: Participant[], pid: string, newAvail: boolean[], qid: string): boolean {
  //@ verify
  //@ decreases ps.length
  //@ ensures idTaken(setAvailInList(ps, pid, newAvail), qid) === idTaken(ps, qid)
  return true
}

export function uniqueIdsPreservedBySetAvail(ps: Participant[], pid: string, newAvail: boolean[]): boolean {
  //@ verify
  //@ requires uniqueIds(ps)
  //@ ensures uniqueIds(setAvailInList(ps, pid, newAvail))
  return true
}

export function uniqueIdsPreservedByRemove(ps: Participant[], pid: string): boolean {
  //@ verify
  //@ requires uniqueIds(ps)
  //@ ensures uniqueIds(removeFromList(ps, pid))
  return true
}

export function idTakenLWW(ps: Participant[], pid: string, avail: boolean[], ts: number, qid: string): boolean {
  //@ verify
  //@ decreases ps.length
  //@ ensures idTaken(setAvailLWW(ps, pid, avail, ts), qid) === idTaken(ps, qid)
  return true
}

export function uniqueIdsPreservedByLWW(ps: Participant[], pid: string, avail: boolean[], ts: number): boolean {
  //@ verify
  //@ requires uniqueIds(ps)
  //@ ensures uniqueIds(setAvailLWW(ps, pid, avail, ts))
  return true
}

// ── Membership-exact freeParticipants (Family F) ──────────────

export function freeParticipantsMembership(ps: Participant[], s: number): boolean {
  //@ verify
  //@ decreases ps.length
  //@ ensures forall(i, 0 <= i && i < freeParticipants(ps, s).length ==> freeAt(freeParticipants(ps, s)[i], s) === true)
  //@ ensures forall(i, 0 <= i && i < ps.length && freeAt(ps[i], s) === true ==> freeParticipants(ps, s).includes(ps[i]))
  return true
}

// ── participantsAt (ids of free participants) ─────────────────

export function freeIdList(ps: Participant[], s: number): string[] {
  //@ verify
  //@ decreases ps.length
  //@ ensures \result.length === countFree(ps, s)
  if (ps.length === 0) return []
  const rest = freeIdList(ps.slice(1), s)
  return freeAt(ps[0], s) ? [ps[0].id, ...rest] : rest
}

export function participantsAt(e: Event, s: number): string[] {
  //@ verify
  //@ requires e.numSlots >= 0 && 0 <= s && s < e.numSlots
  //@ ensures heatmap(e).length === e.numSlots
  //@ ensures \result.length === heatmap(e)[s]
  return freeIdList(e.participants, s)
}

// ── overlap ──────────────────────────────────────────────────

export function pidFreeAt(ps: Participant[], pid: string, s: number): boolean {
  //@ verify
  //@ decreases ps.length
  if (ps.length === 0) return false
  if (ps[0].id === pid && freeAt(ps[0], s)) return true
  return pidFreeAt(ps.slice(1), pid, s)
}

export function allPidsFreeAt(ps: Participant[], pids: string[], s: number): boolean {
  //@ verify
  //@ decreases pids.length
  if (pids.length === 0) return true
  if (!pidFreeAt(ps, pids[0], s)) return false
  return allPidsFreeAt(ps, pids.slice(1), s)
}

export function overlapUpto(ps: Participant[], pids: string[], k: number): boolean[] {
  //@ verify
  //@ requires 0 <= k
  //@ decreases k
  //@ ensures \result.length === k
  //@ ensures forall(s, 0 <= s && s < k ==> \result[s] === allPidsFreeAt(ps, pids, s))
  if (k === 0) return []
  return [...overlapUpto(ps, pids, k - 1), allPidsFreeAt(ps, pids, k - 1)]
}

export function overlap(e: Event, pids: string[]): boolean[] {
  //@ verify
  //@ requires e.numSlots >= 0
  //@ ensures \result.length === e.numSlots
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> \result[s] === allPidsFreeAt(e.participants, pids, s))
  return overlapUpto(e.participants, pids, e.numSlots)
}

// ── Export types & event-level codec (Family E strengthening) ─

interface SparseParticipant {
  id: string
  name: string
  slots: number[]
  updatedAt: number
}

interface SparseEvent {
  id: string
  title: string
  numSlots: number
  participants: SparseParticipant[]
}

export type { SparseParticipant, SparseEvent }

export function encodeParticipant(p: Participant): SparseParticipant {
  //@ verify
  return { id: p.id, name: p.name, slots: sparsify(p.avail), updatedAt: p.updatedAt }
}

export function decodeParticipant(sp: SparseParticipant, n: number): Participant {
  //@ verify
  //@ requires n >= 0
  return { id: sp.id, name: sp.name, avail: densify(sp.slots, n), updatedAt: sp.updatedAt }
}

export function participantRoundTrip(p: Participant): boolean {
  //@ verify
  //@ ensures decodeParticipant(encodeParticipant(p), p.avail.length) === p
  return true
}

export function encodeParticipants(ps: Participant[]): SparseParticipant[] {
  //@ verify
  //@ decreases ps.length
  //@ ensures \result.length === ps.length
  if (ps.length === 0) return []
  return [encodeParticipant(ps[0]), ...encodeParticipants(ps.slice(1))]
}

export function decodeParticipants(sps: SparseParticipant[], n: number): Participant[] {
  //@ verify
  //@ requires n >= 0
  //@ decreases sps.length
  //@ ensures \result.length === sps.length
  if (sps.length === 0) return []
  return [decodeParticipant(sps[0], n), ...decodeParticipants(sps.slice(1), n)]
}

export function encodeEvent(e: Event): SparseEvent {
  //@ verify
  //@ requires e.numSlots >= 0
  return { id: e.id, title: e.title, numSlots: e.numSlots, participants: encodeParticipants(e.participants) }
}

export function decodeEvent(se: SparseEvent): Event {
  //@ verify
  //@ requires se.numSlots >= 0
  return { id: se.id, title: se.title, numSlots: se.numSlots, participants: decodeParticipants(se.participants, se.numSlots) }
}

export function participantsListRoundTrip(ps: Participant[], n: number): boolean {
  //@ verify
  //@ requires n >= 0 && allAvailLen(ps, n)
  //@ decreases ps.length
  //@ ensures decodeParticipants(encodeParticipants(ps), n) === ps
  return true
}

export function eventRoundTrip(e: Event): boolean {
  //@ verify
  //@ requires wellFormed(e)
  //@ ensures decodeEvent(encodeEvent(e)) === e
  return true
}

// ── Query-over-export soundness (Family E2) ───────────────────

export function heatmapOverExport(e: Event): boolean {
  //@ verify
  //@ requires wellFormed(e)
  //@ ensures heatmap(decodeEvent(encodeEvent(e))).length === e.numSlots
  //@ ensures heatmap(e).length === e.numSlots
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> heatmap(decodeEvent(encodeEvent(e)))[s] === heatmap(e)[s])
  return true
}

export function isBestOverExport(e: Event): boolean {
  //@ verify
  //@ requires wellFormed(e)
  //@ ensures isBest(decodeEvent(encodeEvent(e))).length === e.numSlots
  //@ ensures isBest(e).length === e.numSlots
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> isBest(decodeEvent(encodeEvent(e)))[s] === isBest(e)[s])
  return true
}

export function availableAtLeastOverExport(e: Event, k: number): boolean {
  //@ verify
  //@ requires wellFormed(e)
  //@ ensures availableAtLeast(decodeEvent(encodeEvent(e)), k).length === e.numSlots
  //@ ensures availableAtLeast(e, k).length === e.numSlots
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> availableAtLeast(decodeEvent(encodeEvent(e)), k)[s] === availableAtLeast(e, k)[s])
  return true
}

export function overlapOverExport(e: Event, pids: string[]): boolean {
  //@ verify
  //@ requires wellFormed(e)
  //@ ensures overlap(decodeEvent(encodeEvent(e)), pids).length === e.numSlots
  //@ ensures overlap(e, pids).length === e.numSlots
  //@ ensures forall(s, 0 <= s && s < e.numSlots ==> overlap(decodeEvent(encodeEvent(e)), pids)[s] === overlap(e, pids)[s])
  return true
}

// ── Strict well-formedness (A1 + A2 + A3) ────────────────────

export function wellFormedStrict(e: Event): boolean {
  //@ verify
  return wellFormed(e) && uniqueIds(e.participants)
}

export function initEventStrict(id: string, title: string, numSlots: number): boolean {
  //@ verify
  //@ requires numSlots >= 0
  //@ ensures wellFormedStrict(initEvent(id, title, numSlots))
  return true
}

export function applyOpPreservesStrict(e: Event, op: Op): boolean {
  //@ verify
  //@ requires wellFormedStrict(e)
  //@ requires op.kind === "join" ==> !idTaken(e.participants, op.participant.id)
  //@ ensures wellFormedStrict(applyOp(e, op))
  return true
}

export function freshJoinIds(e: Event, ops: Op[]): boolean {
  //@ verify
  //@ decreases ops.length
  if (ops.length === 0) return true
  if (ops[0].kind === "join" && idTaken(e.participants, ops[0].participant.id)) return false
  return freshJoinIds(applyOp(e, ops[0]), ops.slice(1))
}

export function replayPreservesStrict(e: Event, ops: Op[]): boolean {
  //@ verify
  //@ requires wellFormedStrict(e) && freshJoinIds(e, ops)
  //@ decreases ops.length
  //@ ensures wellFormedStrict(replay(e, ops))
  return true
}

// ── Membership-exact participantsAt (Family F) ────────────────

// Explicit witness: the original index in `ps` of the i-th free id. Naming the
// witness (instead of a bare `exists`) keeps the membership postcondition a
// quantifier-alternation-free `forall`, which the verifier discharges reliably.
export function srcIdx(ps: Participant[], s: number, i: number): number {
  //@ verify
  //@ requires 0 <= i && i < freeIdList(ps, s).length
  //@ decreases ps.length
  return freeAt(ps[0], s) ? (i === 0 ? 0 : srcIdx(ps.slice(1), s, i - 1) + 1) : srcIdx(ps.slice(1), s, i) + 1
}

export function freeIdListMembership(ps: Participant[], s: number): boolean {
  //@ verify
  //@ decreases ps.length
  //@ ensures forall(i, 0 <= i && i < freeIdList(ps, s).length ==> 0 <= srcIdx(ps, s, i) && srcIdx(ps, s, i) < ps.length && ps[srcIdx(ps, s, i)].id === freeIdList(ps, s)[i] && freeAt(ps[srcIdx(ps, s, i)], s) === true)
  //@ ensures forall(i, 0 <= i && i < ps.length && freeAt(ps[i], s) === true ==> freeIdList(ps, s).includes(ps[i].id))
  return true
}

// ── Distinct ids under uniqueness ─────────────────────────────

export function stringIn(ss: string[], x: string): boolean {
  //@ verify
  //@ decreases ss.length
  if (ss.length === 0) return false
  if (ss[0] === x) return true
  return stringIn(ss.slice(1), x)
}

export function noDupStrings(ss: string[]): boolean {
  //@ verify
  //@ decreases ss.length
  if (ss.length === 0) return true
  if (stringIn(ss.slice(1), ss[0])) return false
  return noDupStrings(ss.slice(1))
}

export function freeIdListDistinct(ps: Participant[], s: number): boolean {
  //@ verify
  //@ requires uniqueIds(ps)
  //@ decreases ps.length
  //@ ensures noDupStrings(freeIdList(ps, s))
  return true
}
