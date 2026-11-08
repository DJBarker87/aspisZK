import PV_LIB_LeafObservation
import PV_FN_THREAD_f360Outcomes
set_option autoImplicit false
noncomputable section
namespace PV_LIB_ArcClone360
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_EVHB_OwnerMachine
open PV_W1_LeafBoundary PV_W1_OwnerNativeFrame
open PV_THR2_LibrarySemantics_ArcClone

def internalModel {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (effects : Entry → OWNER → Address → Option Data) (v : Valid C e w) :=
  let r := PV_THR2_OwnUniformResourceHandler.lift H
    (.child e.callee e.store.nextActivation e.arguments) w
  (PV_W1_ArgumentEffects.finalStore C e w (effects e w),
    {r with answer := PV_FN_THREAD_f360Outcomes.sourceAnswer v.count r.answer})
def model {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (effects : Entry → OWNER → Address → Option Data) (v : Valid C e w) :=
  PV_LIB.leafObserve (internalModel C e H w effects v)
def law {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (effects : Entry → OWNER → Address → Option Data) (v : Valid C e w)
    (out : PV_LIB.Observation (Answer Data) (Store Data × OWNER) E) : Prop :=
  out = model C e H w effects v

/-- The source guard agrees with the SAME full reply under the existing named
fact. Count writes before abort are retained internally; public abort erases
that state. No success, count bound or identity delta is added at a call. -/
theorem certified {E : Type} (C : Carrier OWNER Data) (e : Entry) (H : Backend E)
    (w : OWNER) (events : List E) (effects : Entry → OWNER → Address → Option Data)
    (pre : PV_W1_ClosedLeaves.Pre e w)
    (semantics : Fact C e H w (effects e w)) (v : Valid C e w) :
    law C e H w effects v
      (PV_LIB.leafObserve (PV_W1_ArgumentEffects.finalStore C e w (effects e w),
        PV_THR2_OwnUniformResourceHandler.lift H
          (.child e.callee e.store.nextActivation e.arguments) w)) ∧
      PV_FN_THREAD_f360.PostFrame C e H w events (effects e w) v := by
  refine ⟨?_,PV_FN_THREAD_f360.contract_frame C e H w events effects pre semantics v⟩
  change _ = PV_LIB.leafObserve (internalModel C e H w effects v)
  unfold internalModel
  dsimp only
  rw [PV_FN_THREAD_f360Outcomes.fact_guard C H effects e w semantics v]
#print axioms certified
end PV_LIB_ArcClone360
