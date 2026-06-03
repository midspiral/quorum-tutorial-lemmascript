//@ backend dafny

// ═══════════════════════════════════════════════════════════════
// Quorum — verified grid coordinate mapping
//
// The UI paints cells at (col, row); the verified core (domain.ts) reasons in
// flat slot indices [0, numSlots). This file is the bridge, and it proves the
// bridge is sound:
//   • in range  — every cell of a numCols × slotsPerDay grid maps into [0, numSlots);
//   • injective — distinct cells never alias the same slot index.
//
// The UI only ever needs the FORWARD map (iterate (col, row), read
// heatmap[gridIndex(...)]), so no integer division is required. Proving these
// two facts shrinks the "slotIndex ⟷ labeling" trusted edge down to just the
// calendar/timezone arithmetic, which stays (unverified) in the shell
// (src/gridShell.ts).
// ═══════════════════════════════════════════════════════════════

// Flat slot index of the cell at (col, row) on a grid with `slotsPerDay` rows.
export function gridIndex(slotsPerDay: number, col: number, row: number): number {
  //@ verify
  //@ requires slotsPerDay >= 1
  //@ requires col >= 0 && row >= 0 && row < slotsPerDay
  //@ ensures \result === col * slotsPerDay + row
  //@ ensures \result >= 0
  //@ ensures \result < (col + 1) * slotsPerDay
  return col * slotsPerDay + row
}

// In range: a cell on a numCols × slotsPerDay grid lands in [0, numCols*slotsPerDay).
export function gridIndexInRange(numCols: number, slotsPerDay: number, col: number, row: number): boolean {
  //@ verify
  //@ requires slotsPerDay >= 1 && numCols >= 0
  //@ requires 0 <= col && col < numCols && 0 <= row && row < slotsPerDay
  //@ ensures 0 <= gridIndex(slotsPerDay, col, row)
  //@ ensures gridIndex(slotsPerDay, col, row) < numCols * slotsPerDay
  return true
}

// Injective: distinct cells never collide on the same slot.
export function gridIndexInjective(slotsPerDay: number, c1: number, r1: number, c2: number, r2: number): boolean {
  //@ verify
  //@ requires slotsPerDay >= 1
  //@ requires c1 >= 0 && c2 >= 0
  //@ requires 0 <= r1 && r1 < slotsPerDay && 0 <= r2 && r2 < slotsPerDay
  //@ requires gridIndex(slotsPerDay, c1, r1) === gridIndex(slotsPerDay, c2, r2)
  //@ ensures c1 === c2 && r1 === r2
  return true
}
