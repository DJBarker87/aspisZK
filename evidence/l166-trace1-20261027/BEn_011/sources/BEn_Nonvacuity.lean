import BEn_AdmittedCuts
import BEl_Nonvacuity
import ARX_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEn_Nonvacuity
open Aeneas Aeneas.Std Result SdkC_Source

/-- The local domain has an observation for either slot, independently of
acceptance. This makes no claim of a real-byte accepted deployment fixture. -/
theorem local (input : BEn_ExtractedSlots.Input) (slot : Fin 2) :
    ∃ (state : Nat) (before : Log),
      BEh_Scope.Law (BEn_ExtractedSlots.native (BEf_Count.call (fun _ => .fail .panic))
        (fun _ => .fail .panic) input slot state before)
        (BEl_NativeBatchCut.source (BEf_Count.call (fun _ => .fail .panic))
          (fun _ => .fail .panic) input slot state before) :=
  ⟨0,[],BEn_LocalAssociation.observation _ _ input slot 0 [] trivial⟩

/-- Recorder failure retains a genuinely issued read and its state update. -/
theorem failed (parts : Parts) (n : Nat) (before : Log) :
    BEn_ExtractedSlots.observe (BEf_Count.call (fun _ => .fail .panic))
      (BEg_Terminal.terminal (BEg_Nonvacuity.accepted parts)) n before =
      (.fail .panic,n+1,before++[⟨parts,.fail .panic⟩]) := by
  unfold BEn_ExtractedSlots.observe
  rw [BEl_PartialRecorder.correspondence]
  exact BEg_Nonvacuity.failed_read parts n before

/-- Positive-query accepted recorder case, reusing the existing witness. -/
theorem success (parts : Parts) (digest : Digest) (n : Nat) (before : Log) :
    BEn_ExtractedSlots.observe (BEf_Count.call (fun _ => .ok digest))
      (BEg_Terminal.terminal (BEg_Nonvacuity.accepted parts)) n before =
      (.ok (.Ok ()),n+1,before++[⟨parts,.ok digest⟩]) := by
  unfold BEn_ExtractedSlots.observe
  rw [BEl_PartialRecorder.correspondence]
  exact BEg_Nonvacuity.success parts digest n before

#print axioms local
#print axioms failed
#print axioms success
#print axioms BEl_Nonvacuity.rejected
#print axioms ARX_Nonvacuity.conditional
end AspisR1.BEn_Nonvacuity
end
