import { Fragment, useRef, useState, useCallback } from "react";
import type { Participant } from "../domain";
import { freeAt } from "../domain";
import type { GridConfig } from "../gridShell";
import { slotIndex, timeLabel, colLabel } from "../gridShell";

interface GridProps {
  gridConfig: GridConfig;
  heatmap: number[];
  best: boolean[];
  max: number;
  mode: "paint" | "group";
  myParticipant: Participant | null;
  onPaint: (slots: number[], value: boolean) => void;
  whoIsFreeAt: (slot: number) => Participant[];
}

function heatColor(count: number, max: number): string {
  if (max === 0 || count === 0) return "transparent";
  const t = count / max;
  const r = Math.round(255 - t * (255 - 5));
  const g = Math.round(255 - t * (255 - 150));
  const b = Math.round(255 - t * (255 - 105));
  return `rgb(${r},${g},${b})`;
}

export default function Grid({
  gridConfig,
  heatmap,
  best,
  max,
  mode,
  myParticipant,
  onPaint,
  whoIsFreeAt,
}: GridProps) {
  const { cols, slotsPerDay } = gridConfig;
  const painting = useRef(false);
  const paintValue = useRef(true);
  const painted = useRef<Set<number>>(new Set());
  const [hoverSlot, setHoverSlot] = useState<number | null>(null);

  const cellFor = useCallback(
    (el: Element | null): { col: number; row: number } | null => {
      if (!el) return null;
      const c = (el as HTMLElement).dataset.col;
      const r = (el as HTMLElement).dataset.row;
      if (c == null || r == null) return null;
      return { col: Number(c), row: Number(r) };
    },
    []
  );

  function handleDown(e: React.PointerEvent) {
    if (mode !== "paint" || !myParticipant) return;
    const cell = cellFor(e.target as Element);
    if (!cell) return;
    e.preventDefault();
    (e.target as HTMLElement).setPointerCapture(e.pointerId);
    const slot = slotIndex(gridConfig, cell.col, cell.row);
    const currentlyFree = freeAt(myParticipant, slot);
    paintValue.current = !currentlyFree;
    painting.current = true;
    painted.current = new Set([slot]);
  }

  function handleMove(e: React.PointerEvent) {
    if (!painting.current) return;
    const el = document.elementFromPoint(e.clientX, e.clientY);
    const cell = cellFor(el);
    if (!cell) return;
    const slot = slotIndex(gridConfig, cell.col, cell.row);
    painted.current.add(slot);
  }

  function handleUp() {
    if (!painting.current) return;
    painting.current = false;
    onPaint([...painted.current], paintValue.current);
    painted.current = new Set();
  }

  function handleHover(e: React.MouseEvent) {
    if (mode !== "group") { setHoverSlot(null); return; }
    const cell = cellFor(e.target as Element);
    if (!cell) { setHoverSlot(null); return; }
    setHoverSlot(slotIndex(gridConfig, cell.col, cell.row));
  }

  const showLabel = (row: number) =>
    gridConfig.slotMinutes >= 60 || row % 2 === 0;

  return (
    <div className="grid-wrapper">
      <div
        className="grid"
        style={{
          gridTemplateColumns: `auto repeat(${cols.length}, 1fr)`,
          gridTemplateRows: `auto repeat(${slotsPerDay}, 1fr)`,
        }}
        onPointerDown={handleDown}
        onPointerMove={handleMove}
        onPointerUp={handleUp}
        onPointerCancel={handleUp}
        onMouseMove={handleHover}
        onMouseLeave={() => setHoverSlot(null)}
      >
        {/* corner */}
        <div className="grid-corner" />

        {/* column headers */}
        {cols.map((_, ci) => (
          <div key={`h${ci}`} className="grid-col-header">
            {colLabel(gridConfig, ci)}
          </div>
        ))}

        {/* rows */}
        {Array.from({ length: slotsPerDay }, (_, row) => (
          <Fragment key={row}>
            <div className="grid-time">
              {showLabel(row) ? timeLabel(gridConfig, row) : ""}
            </div>
            {cols.map((_, col) => {
              const slot = slotIndex(gridConfig, col, row);
              const count = heatmap[slot] ?? 0;
              const isBest = best[slot] ?? false;
              const myFree =
                mode === "paint" && myParticipant
                  ? freeAt(myParticipant, slot)
                  : false;

              return (
                <div
                  key={`${col}-${row}`}
                  className={[
                    "grid-cell",
                    isBest ? "cell-best" : "",
                    myFree && mode === "paint" ? "cell-mine" : "",
                  ]
                    .filter(Boolean)
                    .join(" ")}
                  data-col={col}
                  data-row={row}
                  style={{
                    backgroundColor:
                      mode === "group"
                        ? heatColor(count, max)
                        : myFree
                          ? "var(--color-primary)"
                          : heatColor(count, max),
                  }}
                >
                  {mode === "group" && count > 0 && (
                    <span className="cell-count">{count}</span>
                  )}
                </div>
              );
            })}
          </Fragment>
        ))}
      </div>

      {mode === "group" && hoverSlot !== null && hoverSlot < heatmap.length && (
        <Tooltip slot={hoverSlot} whoIsFreeAt={whoIsFreeAt} />
      )}
    </div>
  );
}

function Tooltip({
  slot,
  whoIsFreeAt,
}: {
  slot: number;
  whoIsFreeAt: (s: number) => Participant[];
}) {
  const free = whoIsFreeAt(slot);
  if (free.length === 0) return null;
  return (
    <div className="tooltip">
      <strong>{free.length} free</strong>
      {free.map(p => (
        <div key={p.id}>{p.name}</div>
      ))}
    </div>
  );
}
