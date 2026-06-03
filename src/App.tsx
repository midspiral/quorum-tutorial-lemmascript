import { useState, useCallback } from "react";
import type { Op, Participant } from "./domain";
import { freeAt } from "./domain";
import type { GridConfig } from "./gridShell";
import { buildGridConfig, totalSlots } from "./gridShell";
import {
  createLocalStore,
  createParticipant,
  getMyPid,
  type QuorumStore,
} from "./store";
import { useQuorum } from "./useQuorum";
import Calendar from "./components/Calendar";
import TimeRangePicker from "./components/TimeRangePicker";
import ParticipantChips from "./components/ParticipantChips";
import Grid from "./components/Grid";

const WEEKDAYS = [
  "Sunday",
  "Monday",
  "Tuesday",
  "Wednesday",
  "Thursday",
  "Friday",
  "Saturday",
];

function Setup({ onCreate }: { onCreate: (s: QuorumStore) => void }) {
  const [title, setTitle] = useState("");
  const [kind, setKind] = useState<"dates" | "weekdays">("dates");
  const [selectedDates, setSelectedDates] = useState<Set<string>>(new Set());
  const [selectedDays, setSelectedDays] = useState<Set<string>>(
    new Set(WEEKDAYS)
  );
  const [startTime, setStartTime] = useState("09:00");
  const [endTime, setEndTime] = useState("17:00");
  const [slotMinutes, setSlotMinutes] = useState(30);

  function toggleDate(iso: string) {
    setSelectedDates((prev) => {
      const next = new Set(prev);
      if (next.has(iso)) next.delete(iso);
      else next.add(iso);
      return next;
    });
  }

  function toggleDay(day: string) {
    setSelectedDays((prev) => {
      const next = new Set(prev);
      if (next.has(day)) next.delete(day);
      else next.add(day);
      return next;
    });
  }

  function handleCreate() {
    const cols =
      kind === "dates"
        ? [...selectedDates].sort()
        : WEEKDAYS.filter((d) => selectedDays.has(d));
    if (cols.length === 0) return;
    const config = buildGridConfig(kind, cols, startTime, endTime, slotMinutes);
    const id = crypto.randomUUID();
    const store = createLocalStore(id, title || "Untitled Event", config);
    onCreate(store);
  }

  const cols =
    kind === "dates"
      ? [...selectedDates].sort()
      : WEEKDAYS.filter((d) => selectedDays.has(d));
  const canCreate = cols.length > 0;

  return (
    <div className="setup">
      <h1>Quorum</h1>
      <p className="subtitle">Find the time that works for everyone</p>

      <label className="field">
        Event name
        <input
          type="text"
          value={title}
          onChange={(e) => setTitle(e.target.value)}
          placeholder="e.g. Team sync"
        />
      </label>

      <div className="mode-toggle">
        <button
          className={kind === "dates" ? "active" : ""}
          onClick={() => setKind("dates")}
        >
          Specific Dates
        </button>
        <button
          className={kind === "weekdays" ? "active" : ""}
          onClick={() => setKind("weekdays")}
        >
          Days of Week
        </button>
      </div>

      {kind === "dates" ? (
        <Calendar selectedDates={selectedDates} onToggleDate={toggleDate} />
      ) : (
        <div className="weekday-chips">
          {WEEKDAYS.map((d) => (
            <button
              key={d}
              className={`chip${selectedDays.has(d) ? " chip-selected" : ""}`}
              onClick={() => toggleDay(d)}
            >
              {d.slice(0, 3)}
            </button>
          ))}
        </div>
      )}

      <TimeRangePicker
        startTime={startTime}
        endTime={endTime}
        slotMinutes={slotMinutes}
        onChangeStart={setStartTime}
        onChangeEnd={setEndTime}
        onChangeSlotMinutes={setSlotMinutes}
      />

      <button className="btn-primary" onClick={handleCreate} disabled={!canCreate}>
        Create Event
      </button>
    </div>
  );
}

function EventView({ store }: { store: QuorumStore }) {
  const { event, heatmap, best, max, whoIsFreeAt, dispatch } =
    useQuorum(store);
  const gridConfig = store.getGridConfig();
  const [mode, setMode] = useState<"paint" | "group">("paint");
  const [name, setName] = useState("");
  const myPid = getMyPid();

  const myParticipant: Participant | undefined = event.participants.find(
    (p) => p.id === myPid
  );
  const hasJoined = !!myParticipant;

  function handleJoin() {
    if (!name.trim()) return;
    const p = createParticipant(name.trim(), event.numSlots);
    dispatch({ kind: "join", participant: p });
    setName("");
  }

  const handlePaint = useCallback(
    (slots: number[], value: boolean) => {
      if (!myParticipant) return;
      const newAvail = [...myParticipant.avail];
      for (const s of slots) {
        if (s >= 0 && s < newAvail.length) newAvail[s] = value;
      }
      const op: Op = {
        kind: "paint",
        pid: myParticipant.id,
        avail: newAvail,
        ts: 0,
      };
      dispatch(op);
    },
    [myParticipant, dispatch]
  );

  return (
    <div className="event-view">
      <h2>{event.title}</h2>
      <ParticipantChips participants={event.participants} myPid={myPid} />

      {!hasJoined && (
        <div className="join-bar">
          <input
            type="text"
            value={name}
            onChange={(e) => setName(e.target.value)}
            placeholder="Your name"
            onKeyDown={(e) => e.key === "Enter" && handleJoin()}
          />
          <button className="btn-primary" onClick={handleJoin}>
            Join
          </button>
        </div>
      )}

      <div className="mode-toggle">
        <button
          className={mode === "paint" ? "active" : ""}
          onClick={() => setMode("paint")}
          disabled={!hasJoined}
        >
          Paint
        </button>
        <button
          className={mode === "group" ? "active" : ""}
          onClick={() => setMode("group")}
        >
          Group
        </button>
      </div>

      <Grid
        gridConfig={gridConfig}
        heatmap={heatmap}
        best={best}
        max={max}
        mode={mode}
        myParticipant={myParticipant ?? null}
        onPaint={handlePaint}
        whoIsFreeAt={whoIsFreeAt}
      />
    </div>
  );
}

export default function App() {
  const [store, setStore] = useState<QuorumStore | null>(null);

  if (!store) return <Setup onCreate={setStore} />;
  return <EventView store={store} />;
}
