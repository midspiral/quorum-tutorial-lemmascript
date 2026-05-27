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

export function slotIndex(config: GridConfig, col: number, row: number): number {
  return col * config.slotsPerDay + row;
}

export function slotToCell(
  config: GridConfig,
  slot: number
): { col: number; row: number } {
  return {
    col: Math.floor(slot / config.slotsPerDay),
    row: slot % config.slotsPerDay,
  };
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
