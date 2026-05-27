import { useState } from "react";

interface CalendarProps {
  selectedDates: Set<string>;
  onToggleDate: (iso: string) => void;
}

const DAY_HEADERS = ["Su", "Mo", "Tu", "We", "Th", "Fr", "Sa"];

function daysInMonth(year: number, month: number): number {
  return new Date(year, month + 1, 0).getDate();
}

function startDow(year: number, month: number): number {
  return new Date(year, month, 1).getDay();
}

function toIso(year: number, month: number, day: number): string {
  const m = String(month + 1).padStart(2, "0");
  const d = String(day).padStart(2, "0");
  return `${year}-${m}-${d}`;
}

const MONTH_NAMES = [
  "January","February","March","April","May","June",
  "July","August","September","October","November","December",
];

export default function Calendar({ selectedDates, onToggleDate }: CalendarProps) {
  const now = new Date();
  const [year, setYear] = useState(now.getFullYear());
  const [month, setMonth] = useState(now.getMonth());

  const days = daysInMonth(year, month);
  const offset = startDow(year, month);

  function prev() {
    if (month === 0) { setYear(y => y - 1); setMonth(11); }
    else setMonth(m => m - 1);
  }
  function next() {
    if (month === 11) { setYear(y => y + 1); setMonth(0); }
    else setMonth(m => m + 1);
  }

  const cells: (number | null)[] = [];
  for (let i = 0; i < offset; i++) cells.push(null);
  for (let d = 1; d <= days; d++) cells.push(d);

  return (
    <div className="calendar">
      <div className="calendar-nav">
        <button onClick={prev} className="btn-icon">&larr;</button>
        <span className="calendar-title">{MONTH_NAMES[month]} {year}</span>
        <button onClick={next} className="btn-icon">&rarr;</button>
      </div>
      <div className="calendar-grid">
        {DAY_HEADERS.map(d => (
          <div key={d} className="calendar-header">{d}</div>
        ))}
        {cells.map((day, i) => {
          if (day === null) return <div key={`e${i}`} />;
          const iso = toIso(year, month, day);
          const selected = selectedDates.has(iso);
          return (
            <button
              key={iso}
              className={`calendar-day${selected ? " selected" : ""}`}
              onClick={() => onToggleDate(iso)}
            >
              {day}
            </button>
          );
        })}
      </div>
    </div>
  );
}
