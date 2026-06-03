// Trusted grid labeling + configuration. The only real logic here — the
// cell→slot map (`slotIndex`) — delegates to the *verified* gridIndex
// (src/grid.ts), which proves it is in-range and injective. Columns may be
// specific calendar dates OR abstract days of the week; the verified core is
// agnostic (it only ever sees numSlots), so that distinction lives entirely in
// the (trusted) labeling below.

import { gridIndex } from "./grid";

export interface GridConfig {
  kind: "dates" | "weekdays";
  cols: string[];
  slotsPerDay: number;
  startTime: string;
  slotMinutes: number;
}

export function totalSlots(config: GridConfig): number {
  return config.cols.length * config.slotsPerDay;
}

// Cell (col, row) → flat slot index, via the verified forward map.
export function slotIndex(config: GridConfig, col: number, row: number): number {
  return gridIndex(config.slotsPerDay, col, row);
}

function parseTime(t: string): number {
  const [h, m] = t.split(":").map(Number);
  return h * 60 + m;
}

function formatTime(totalMinutes: number): string {
  const h = Math.floor(totalMinutes / 60) % 24;
  const m = totalMinutes % 60;
  const suffix = h >= 12 ? "PM" : "AM";
  const h12 = h === 0 ? 12 : h > 12 ? h - 12 : h;
  return `${h12}:${m.toString().padStart(2, "0")} ${suffix}`;
}

export function timeLabel(config: GridConfig, row: number): string {
  const startMinutes = parseTime(config.startTime);
  return formatTime(startMinutes + row * config.slotMinutes);
}

export function buildGridConfig(
  kind: "dates" | "weekdays",
  cols: string[],
  startTime: string,
  endTime: string,
  slotMinutes: number
): GridConfig {
  const rangeMinutes = parseTime(endTime) - parseTime(startTime);
  const slotsPerDay = Math.max(1, Math.floor(rangeMinutes / slotMinutes));
  return { kind, cols, slotsPerDay, startTime, slotMinutes };
}

const SHORT_DAYS = ["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"];

export function colLabel(config: GridConfig, col: number): string {
  const raw = config.cols[col];
  if (config.kind === "weekdays") return raw;
  const d = new Date(raw + "T00:00");
  return `${SHORT_DAYS[d.getUTCDay()]} ${d.getUTCMonth() + 1}/${d.getUTCDate()}`;
}
