import type { Event, Op, Participant } from "./domain";
import { applyOp, initEvent } from "./domain";
import type { GridConfig } from "./gridShell";
import { totalSlots } from "./gridShell";

export interface QuorumStore {
  getSnapshot(): Event;
  getGridConfig(): GridConfig;
  subscribe(listener: () => void): () => void;
  dispatch(op: Op): void;
}

interface Persisted {
  event: Event;
  gridConfig: GridConfig;
  clock: number;
}

const STORE_PREFIX = "quorum:";
const PID_KEY = "quorum:myPid";

function storageKey(eventId: string) {
  return STORE_PREFIX + eventId;
}

function save(eventId: string, data: Persisted) {
  try {
    localStorage.setItem(storageKey(eventId), JSON.stringify(data));
  } catch {
    // storage full or unavailable — continue without persistence
  }
}

function load(eventId: string): Persisted | null {
  try {
    const raw = localStorage.getItem(storageKey(eventId));
    if (!raw) return null;
    return JSON.parse(raw) as Persisted;
  } catch {
    return null;
  }
}

export function createLocalStore(
  eventId: string,
  title: string,
  gridConfig: GridConfig
): QuorumStore {
  const existing = load(eventId);
  let event: Event;
  let cfg: GridConfig;
  let clock: number;

  if (existing && existing.event.numSlots === totalSlots(gridConfig)) {
    event = existing.event;
    cfg = existing.gridConfig;
    clock = existing.clock;
  } else {
    event = initEvent(eventId, title, totalSlots(gridConfig));
    cfg = gridConfig;
    clock = Date.now();
  }

  const listeners = new Set<() => void>();

  function notify() {
    for (const fn of listeners) fn();
  }

  return {
    getSnapshot() {
      return event;
    },
    getGridConfig() {
      return cfg;
    },
    subscribe(listener) {
      listeners.add(listener);
      return () => {
        listeners.delete(listener);
      };
    },
    dispatch(op: Op) {
      if (op.kind === "paint") {
        clock = Math.max(clock + 1, Date.now());
        op = { ...op, ts: clock };
      }
      event = applyOp(event, op);
      save(eventId, { event, gridConfig: cfg, clock });
      notify();
    },
  };
}

export function createParticipant(
  name: string,
  numSlots: number
): Participant {
  const id = getOrCreateMyPid();
  return {
    id,
    name,
    avail: new Array<boolean>(numSlots).fill(false),
    updatedAt: 0,
  };
}

export function getOrCreateMyPid(): string {
  let pid = localStorage.getItem(PID_KEY);
  if (!pid) {
    pid = crypto.randomUUID();
    localStorage.setItem(PID_KEY, pid);
  }
  return pid;
}

export function getMyPid(): string | null {
  return localStorage.getItem(PID_KEY);
}
