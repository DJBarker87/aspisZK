import R1Z.PDict_TapeTrace244
set_option autoImplicit false
namespace R1Z.PDict_EventWorld244
open PDict_TapeCore244

structure Event (Q R : Type) where
  request : Q
  reply : R

/-- Entropy is a parameter, so the sibling's exact RawTape type can be used.
The OS event tape is additional state, never a replacement entropy carrier. -/
structure World (T Q R : Type) where
  entropy : T
  entropyUsed : Nat
  files : List (Event Q R)
  fileUsed : Nat

def tape {T Q R : Type} (world : World T Q R) : Tape (Event Q R) :=
  ⟨world.files,world.fileUsed⟩

def step {T Q R : Type} [DecidableEq Q] (request : Q) (world : World T Q R) :
    Option (R × World T Q R) := do
  let (event, _) ← PDict_TapeCore244.read (tape world)
  if event.request = request then
    some (event.reply,{ world with fileUsed := world.fileUsed+1 })
  else none

theorem step_at {T Q R : Type} [DecidableEq Q] (world : World T Q R)
    (event : Event Q R) (h : world.files[world.fileUsed]? = some event) :
    step event.request world =
      some (event.reply,{ world with fileUsed := world.fileUsed+1 }) := by
  simp [step, PDict_TapeCore244.read, tape, h]

theorem exhausted {T Q R : Type} [DecidableEq Q] (world : World T Q R)
    (request : Q) (h : world.files[world.fileUsed]? = none) :
    step request world = none := by
  simp [step,PDict_TapeCore244.read,tape,h]

theorem mismatch {T Q R : Type} [DecidableEq Q] (world : World T Q R)
    (request : Q) (event : Event Q R)
    (h : world.files[world.fileUsed]? = some event) (different : event.request ≠ request) :
    step request world = none := by
  simp [step,PDict_TapeCore244.read,tape,h,different]

theorem success {T Q R : Type} [DecidableEq Q] (world next : World T Q R)
    (request : Q) (reply : R) (run : step request world = some (reply,next)) :
    ∃ event : Event Q R, world.files[world.fileUsed]? = some event ∧
      event.request = request ∧ event.reply = reply ∧
      next = { world with fileUsed := world.fileUsed+1 } := by
  cases h : world.files[world.fileUsed]? with
  | none => simp [step,PDict_TapeCore244.read,tape,h] at run
  | some event =>
    by_cases same : event.request = request
    · have eq : event.reply = reply ∧
          { world with fileUsed := world.fileUsed+1 } = next := by
        simpa [step,PDict_TapeCore244.read,tape,h,same] using run
      exact ⟨event,rfl,same,eq.1,eq.2.symm⟩
    · simp [step,PDict_TapeCore244.read,tape,h,same] at run

theorem inventory {T Q R : Type} [DecidableEq Q] (world next : World T Q R)
    (request : Q) (reply : R) (run : step request world = some (reply,next)) :
    next.entropy = world.entropy ∧ next.entropyUsed = world.entropyUsed ∧
    next.files = world.files ∧ next.fileUsed = world.fileUsed+1 := by
  obtain ⟨_,_,_,_,eq⟩ := success world next request reply run
  rw [eq]
  exact ⟨rfl,rfl,rfl,rfl⟩

def Admitted {T Q R : Type} (law : Q → R → Prop) (world : World T Q R) : Prop :=
  ∀ event ∈ world.files, law event.request event.reply

theorem law_at {T Q R : Type} [DecidableEq Q] (law : Q → R → Prop)
    (world next : World T Q R) (request : Q) (reply : R)
    (admitted : Admitted law world) (run : step request world = some (reply,next)) :
    law request reply := by
  obtain ⟨event,h,same,value,_⟩ := success world next request reply run
  rw [←same,←value]
  exact admitted event (List.mem_of_getElem? h)

theorem admission_frame {T Q R : Type} [DecidableEq Q] (law : Q → R → Prop)
    (world next : World T Q R) (request : Q) (reply : R)
    (admitted : Admitted law world) (run : step request world = some (reply,next)) :
    Admitted law next := by
  obtain ⟨_,_,_,_,eq⟩ := success world next request reply run
  rw [eq]
  exact admitted

#print axioms step_at
#print axioms exhausted
#print axioms mismatch
#print axioms success
#print axioms inventory
#print axioms law_at
#print axioms admission_frame
end R1Z.PDict_EventWorld244
