import NIV_ExtractedForward
import NGL_EntryRouting
import NIS_AdmissionSdk
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIV_ForwardPacket
open Aeneas Aeneas.Std Result
/-- A typed boundary cut: complete child replies contain their state and effects.
    No success is asserted and no observation is used as an input premise. -/
def ops {Account State Event : Type}
    (children : NGL_EntryRouting.Children Account State Event) (state : State) :
    Hiq_DispatchSource.Ops Account where
  first := fun p a d => (children.first p a d state).result
  second := fun p a d => (children.second p a d state).result
  init := fun _ _ _ => fail .panic
  write := fun _ _ _ => fail .panic
  finalize := fun _ _ _ => fail .panic

theorem result {Account State Event : Type}
    (children : NGL_EntryRouting.Children Account State Event) (state : State)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8) :
    (NGL_EntryRouting.run children p a d state).1.result =
      NIV_ExtractedForward.entry (ops children state) p a d := by
  rw [NIV_ExtractedForward.entry_source]
  exact NGL_EntryRouting.source children p a d state (ops children state) rfl rfl

/-- On each admitted route the full reply and single call record are exactly the
    selected child applied to the original descriptors and pre-state. -/
theorem first {Account State Event : Type}
    (children : NGL_EntryRouting.Children Account State Event) (state : State)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8)
    (selected : Hiq_ReleaseRoute.route d = .first) :
    NGL_EntryRouting.run children p a d state =
      (children.first p a d state,[.first p a d]) := by
  simp only [NGL_EntryRouting.run, selected]

theorem second {Account State Event : Type}
    (children : NGL_EntryRouting.Children Account State Event) (state : State)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8)
    (selected : Hiq_ReleaseRoute.route d = .second) :
    NGL_EntryRouting.run children p a d state =
      (children.second p a d state,[.second p a d]) := by
  simp only [NGL_EntryRouting.run, selected]

theorem rejected {Account State Event : Type}
    (children : NGL_EntryRouting.Children Account State Event) (state : State)
    (p : Hiq_DispatchSource.Key) (a : Slice Account) (d : Slice U8)
    (selected : Hiq_ReleaseRoute.route d = .reject) :
    NGL_EntryRouting.run children p a d state =
      (⟨ok (.Err .InvalidInstructionData),state,[]⟩,[]) :=
  NGL_EntryRouting.rejected_frame children p a d state selected

#print axioms result
#print axioms first
#print axioms second
#print axioms rejected
end AspisR1.NIV_ForwardPacket
end
