interface TimeRangePickerProps {
  startTime: string;
  endTime: string;
  slotMinutes: number;
  onChangeStart: (t: string) => void;
  onChangeEnd: (t: string) => void;
  onChangeSlotMinutes: (m: number) => void;
}

function timeOptions(): string[] {
  const opts: string[] = [];
  for (let h = 0; h < 24; h++) {
    for (const m of [0, 30]) {
      opts.push(`${String(h).padStart(2, "0")}:${String(m).padStart(2, "0")}`);
    }
  }
  opts.push("24:00");
  return opts;
}

function formatOption(t: string): string {
  if (t === "24:00") return "12:00 AM (next day)";
  const [h, m] = t.split(":").map(Number);
  const suffix = h >= 12 ? "PM" : "AM";
  const h12 = h === 0 ? 12 : h > 12 ? h - 12 : h;
  return `${h12}:${String(m).padStart(2, "0")} ${suffix}`;
}

const TIMES = timeOptions();

export default function TimeRangePicker({
  startTime,
  endTime,
  slotMinutes,
  onChangeStart,
  onChangeEnd,
  onChangeSlotMinutes,
}: TimeRangePickerProps) {
  return (
    <div className="time-range">
      <label>
        From
        <select value={startTime} onChange={e => onChangeStart(e.target.value)}>
          {TIMES.map(t => (
            <option key={t} value={t}>{formatOption(t)}</option>
          ))}
        </select>
      </label>
      <label>
        To
        <select value={endTime} onChange={e => onChangeEnd(e.target.value)}>
          {TIMES.map(t => (
            <option key={t} value={t}>{formatOption(t)}</option>
          ))}
        </select>
      </label>
      <label>
        Every
        <select
          value={slotMinutes}
          onChange={e => onChangeSlotMinutes(Number(e.target.value))}
        >
          <option value={15}>15 min</option>
          <option value={30}>30 min</option>
          <option value={60}>60 min</option>
        </select>
      </label>
    </div>
  );
}
