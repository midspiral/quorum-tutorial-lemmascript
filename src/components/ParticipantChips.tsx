import type { Participant } from "../domain";

interface ParticipantChipsProps {
  participants: Participant[];
  myPid: string | null;
}

export default function ParticipantChips({
  participants,
  myPid,
}: ParticipantChipsProps) {
  if (participants.length === 0) return null;
  return (
    <div className="participant-chips">
      {participants.map(p => (
        <span
          key={p.id}
          className={`chip${p.id === myPid ? " chip-me" : ""}`}
        >
          {p.name}
        </span>
      ))}
    </div>
  );
}
