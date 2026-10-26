import R1Z.PDict_EventReplay244
set_option autoImplicit false
namespace R1Z.PDict_TapeCore244

theorem read_suffix {A : Type} (t next : Tape A) (reply : A)
    (run : read t = some (reply,next)) :
    t.replies.drop t.used = reply :: next.replies.drop next.used := by
  obtain ⟨position,same,used⟩ := read_success t next reply run
  rw [same,used]
  have split := List.drop_eq_getElem?_toList_append (l:=t.replies) (i:=t.used)
  simpa only [position,Option.toList_some,List.singleton_append] using split

/-- The whole consumed sequence, including errors and rejected replies, is the
actual contiguous prefix at the incoming cursor. The unconsumed suffix agrees. -/
theorem replay_suffix {A : Type} {t final : Tape A} {out : List A}
    (trace : Replay t out final) :
    t.replies.drop t.used = out ++ final.replies.drop final.used := by
  induction trace with
  | nil t => rfl
  | cons head tail ih =>
    rw [read_suffix _ _ _ head,ih]
    rfl

theorem reads_suffix {A : Type} (n : Nat) (t final : Tape A) (out : List A)
    (run : reads n t = some (out,final)) :
    t.replies.drop t.used = out ++ final.replies.drop final.used :=
  replay_suffix (reads_replay n t final out run)

#print axioms read_suffix
#print axioms replay_suffix
#print axioms reads_suffix
end R1Z.PDict_TapeCore244

namespace R1Z.PDict_EventWorld244
theorem replay_suffix {T Q R : Type} [DecidableEq Q] {world final : World T Q R}
    {events : List (Event Q R)} (trace : Replay world events final) :
    world.files.drop world.fileUsed = events ++ final.files.drop final.fileUsed :=
  PDict_TapeCore244.replay_suffix (to_tape trace)

#print axioms replay_suffix
end R1Z.PDict_EventWorld244
