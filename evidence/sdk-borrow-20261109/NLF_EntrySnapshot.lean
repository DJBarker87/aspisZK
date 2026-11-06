import NLF_SnapshotEvents
import NLF_InitialBinding
set_option autoImplicit false
namespace NLF_EntrySnapshot
open AspisR1 NLF_RefCell NLF_SdkModel NLF_ParentModel NLF_RuntimeInterpretation NLF_SnapshotEvents

theorem payload (s : State) (a t : Nat)
    (free : (s.cells (s.accounts a).data).writer=none)
    (empty : (s.cells (s.accounts a).data).readers=[]) :
    NLF_Bracket.snapshot s a t = (s,.ok (s.cells (s.accounts a).data).payload) := by
  apply NLF_Bracket.snapshot_ok _ _ _ free <;> simp [empty]

theorem at_entry {F : Type} (h : S2Trust.Heap F) (records : Nat → Account)
    (money : Nat → Nat) (a t : Nat) :
    let p := {install h records money with next:=t}
    let g : Guard := ⟨(h.accounts a).1,t,.shared⟩
    step p a =
      (⟨p.state,t+1,[.acquire a t .shared (.ok g),
        .deref g (.ok (p.state.cells g.cell).payload),.release g (.ok ())]⟩,
       .ok (p.state.cells g.cell).payload) := by
  dsimp only
  unfold step
  rw [payload _ a t (by rfl) (by rfl)]
  simp [events,try_borrow_data,wrap,shared,install,NLF_Admission.initial]

#print axioms payload
#print axioms at_entry
end NLF_EntrySnapshot
