import NLF_EntrySnapshot
import NLF_SnapshotFold
set_option autoImplicit false
namespace NLF_SnapshotOccurrence
open AspisR1 NLF_RefCell NLF_SdkModel NLF_ParentModel NLF_RuntimeInterpretation NLF_SnapshotFold

theorem packet {F : Type} (h : S2Trust.Heap F) (records : Nat → Account) (money : Nat → Nat)
    (prior : List Nat) (a : Nat) :
    let p := (run (install h records money) prior).1
    let r := NLF_SnapshotEvents.step p a
    let g : Guard := ⟨(h.accounts a).1,prior.length,.shared⟩
    r.1.state=(install h records money).state ∧ r.1.next=prior.length+1 ∧
    r.2=.ok ((install h records money).state.cells g.cell).payload ∧
    r.1.events=schedule (install h records money).state 0 prior ++
      [.acquire a prior.length .shared (.ok g),
       .deref g (.ok ((install h records money).state.cells g.cell).payload),.release g (.ok ())] := by
  dsimp only
  have frame := run_frame (install h records money) prior
  have nt := run_next (install h records money) prior
  have ev := run_events (install h records money) prior
  have free : (((run (install h records money) prior).1.state).cells
      (((run (install h records money) prior).1.state).accounts a).data).writer=none := by
    rw [frame]; rfl
  have empty : (((run (install h records money) prior).1.state).cells
      (((run (install h records money) prior).1.state).accounts a).data).readers=[] := by
    rw [frame]; rfl
  refine ⟨(NLF_SnapshotEvents.step_frame _ a).trans frame,?_,?_,?_⟩
  · simpa [install,NLF_SnapshotEvents.step] using nt
  · change (NLF_Bracket.snapshot _ _ _).2= _
    rw [NLF_EntrySnapshot.payload _ a _ free empty,frame]
    rfl
  · have e := NLF_SnapshotEvents.step_ok_events (run (install h records money) prior).1 a free
        (by simp [empty]) (by simp [empty])
    rw [e,frame,nt,ev]
    simp [install,NLF_Admission.initial]


#print axioms packet
end NLF_SnapshotOccurrence
