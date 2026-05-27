import { useSyncExternalStore, useMemo, useCallback } from "react";
import type { Event, Participant, Op } from "./domain";
import {
  heatmap as computeHeatmap,
  isBest as computeIsBest,
  maxCount as computeMaxCount,
  whoIsFree,
} from "./domain";
import type { QuorumStore } from "./store";

export interface QuorumView {
  event: Event;
  heatmap: number[];
  best: boolean[];
  max: number;
  whoIsFreeAt(slot: number): Participant[];
  dispatch(op: Op): void;
}

export function useQuorum(store: QuorumStore): QuorumView {
  const event = useSyncExternalStore(store.subscribe, store.getSnapshot);

  const heatmap = useMemo(() => computeHeatmap(event), [event]);
  const best = useMemo(() => computeIsBest(event), [event]);
  const max = useMemo(() => computeMaxCount(heatmap), [heatmap]);

  const whoIsFreeAt = useCallback(
    (slot: number) => whoIsFree(event, slot),
    [event]
  );

  return { event, heatmap, best, max, whoIsFreeAt, dispatch: store.dispatch };
}
