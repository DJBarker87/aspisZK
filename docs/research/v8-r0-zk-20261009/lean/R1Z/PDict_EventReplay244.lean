import R1Z.PDict_EventWorld244
set_option autoImplicit false
namespace R1Z.PDict_EventWorld244

theorem lookup {T Q R : Type} [DecidableEq Q] (world next : World T Q R)
    (request : Q) (reply : R) (run : step request world = some (reply,next)) :
    world.files[world.fileUsed]? = some (⟨request,reply⟩ : Event Q R) := by
  obtain ⟨event,h,same,value,_⟩ := success world next request reply run
  have eq : event = (⟨request,reply⟩ : Event Q R) := by
    cases event with
    | mk q r => simp only at same value; cases same; cases value; rfl
  rw [eq] at h
  exact h

inductive Replay {T Q R : Type} [DecidableEq Q] :
    World T Q R → List (Event Q R) → World T Q R → Prop
  | nil (world : World T Q R) : Replay world [] world
  | cons {world next final : World T Q R} {event : Event Q R} {rest : List (Event Q R)}
      (head : step event.request world = some (event.reply,next))
      (tail : Replay next rest final) : Replay world (event::rest) final

theorem to_tape {T Q R : Type} [DecidableEq Q] {world final : World T Q R}
    {events : List (Event Q R)} (trace : Replay world events final) :
    PDict_TapeCore244.Replay (tape world) events (tape final) := by
  induction trace with
  | nil world => exact .nil (tape world)
  | @cons world next final event rest head tail ih =>
    have position :=  lookup world next event.request event.reply head
    have eq : next = {world with fileUsed := world.fileUsed+1} := by
      obtain ⟨_,_,_,_,eq⟩ := success world next event.request event.reply head
      exact eq
    have hread : PDict_TapeCore244.read (tape world) = some (event,tape next) := by
      rw [eq]
      apply PDict_TapeCore244.read_at
      exact position
    exact .cons hread ih

theorem replay_inventory {T Q R : Type} [DecidableEq Q] {world final : World T Q R}
    {events : List (Event Q R)} (trace : Replay world events final) :
    final.entropy = world.entropy ∧ final.entropyUsed = world.entropyUsed ∧
    final.files = world.files ∧ final.fileUsed = world.fileUsed+events.length := by
  induction trace with
  | nil world => exact ⟨rfl,rfl,rfl,rfl⟩
  | @cons world next final event rest head tail ih =>
    obtain ⟨entropy,entropyUsed,files,fileUsed⟩ :=
      inventory world next event.request event.reply head
    exact ⟨ih.1.trans entropy,ih.2.1.trans entropyUsed,ih.2.2.1.trans files,
      by simp only [List.length_cons]; omega⟩

theorem replay_append {T Q R : Type} [DecidableEq Q]
    {world middle final : World T Q R} {left right : List (Event Q R)}
    (first : Replay world left middle) (second : Replay middle right final) :
    Replay world (left++right) final := by
  induction first with
  | nil world => exact second
  | cons head tail ih => exact .cons head (ih second)

theorem replay_laws {T Q R : Type} [DecidableEq Q] (law : Q → R → Prop)
    {world final : World T Q R} {events : List (Event Q R)}
    (admitted : Admitted law world) (trace : Replay world events final) :
    ∀ event ∈ events, law event.request event.reply := by
  induction trace with
  | nil => simp only [List.not_mem_nil, false_implies, implies_true]
  | @cons world next final event rest head tail ih =>
    intro e member
    rcases List.mem_cons.mp member with same | later
    · subst e
      exact law_at law world next event.request event.reply admitted head
    · exact ih (admission_frame law world next event.request event.reply admitted head) e later

#print axioms lookup
#print axioms to_tape
#print axioms replay_inventory
#print axioms replay_append
#print axioms replay_laws
end R1Z.PDict_EventWorld244
