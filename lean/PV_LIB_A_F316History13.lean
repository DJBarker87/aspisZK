import PV_LIB_A_F316Prefix13
import PV_LIB_A_F316Full41013
import PV_LIB_A_F316ToInvoke13
import PV_LIB_A_F316Enter22013
import PV_LIB_A_SourceContinuation12
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F316History13
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11
abbrev liftSteps := PV_LIB_A_SourceContinuation12.steps
abbrev liftAfter := PV_LIB_A_SourceContinuation12.after
abbrev programs := PV_LIB_A_F316Enter22013.programs

def stage1 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F316Prefix13.after C ) q

def stage2 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F316Full41013.after C H) (stage1 C H q)

def stage3 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F316ToInvoke13.after C ) (stage2 C H q)

def stage4 (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftAfter (PV_LIB_A_F316Enter22013.after C ) (stage3 C H q)

def steps (C : Carrier OWNER Data) (H : Handler) (q : SourceState) :=
  liftSteps (PV_LIB_A_F316Prefix13.steps C) q +
  liftSteps (PV_LIB_A_F316Full41013.steps C) (stage1 C H q) +
  liftSteps (PV_LIB_A_F316ToInvoke13.steps C) (stage2 C H q) +
  liftSteps (PV_LIB_A_F316Enter22013.steps C) (stage3 C H q)

/-- Callback BODY-entry through full410, source preparations and actual11187
entry into220, or the first earlier stop. This does not assert that the original
f6 history has reached this entry, or that410 supplied a valid native FnOnce. -/
theorem run (C : Carrier PV_EVHB_OwnerMachine.OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : SourceState) :
    PV_LIB_A_PrefixMachine11.advance C K (programs P) resources encode H values (steps C H q) q = stage4 C H q := by
  have h1 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F316Prefix13.steps C) (PV_LIB_A_F316Prefix13.after C )
    (PV_LIB_A_F316Prefix13.run C K (programs P) resources encode H values) q
  change _ = stage1 C H q at h1
  have h2 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F316Full41013.steps C) (PV_LIB_A_F316Full41013.after C H)
    (PV_LIB_A_F316Full41013.run C K (PV_THR2_SourceTraitDispatch.resolve P) resources encode H values) (stage1 C H q)
  change _ = stage2 C H q at h2
  have h3 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F316ToInvoke13.steps C) (PV_LIB_A_F316ToInvoke13.after C )
    (PV_LIB_A_F316ToInvoke13.run C K (programs P) resources encode H values) (stage2 C H q)
  change _ = stage3 C H q at h3
  have h4 := PV_LIB_A_SourceContinuation12.run C K (programs P) resources encode H values
    (PV_LIB_A_F316Enter22013.steps C) (PV_LIB_A_F316Enter22013.after C )
    (PV_LIB_A_F316Enter22013.run C K P resources encode H values) (stage3 C H q)
  change _ = stage4 C H q at h4
  unfold steps
  rw [advance_add,advance_add,advance_add,h1,h2,h3]
  exact h4

#print axioms steps
#print axioms stage4
#print axioms run
end PV_LIB_A_F316History13
