import WAdm_Accepted
import WAdm_OriginalAccepted
import Tx1Q_Nonvacuity
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Nonvacuity
open Tx1Q_Carriers Port2_Initial

def prepared : S.P :=
  ⟨.S2,Array.repeat 2#usize (Array.repeat 32#usize 0#u8),zeroE,zeroE,
    Array.repeat 2#usize zeroE,zeroK,Array.repeat 22#usize 0#u32,
    Array.repeat 10#usize zeroK,Array.repeat 2#usize ⟨zeroK,zeroK⟩,zeroE,
    Array.repeat 32#usize 0#u8⟩
def accumulator : S.A :=
  ⟨⟨List.replicate 64 zeroK,by simp only [List.length_replicate]; scalar_tac⟩,zeroE,zeroK,10#usize⟩

theorem domain_nonempty : ∃ proof pub : Slice U8,
    WAdm_Domain.Admitted prepared accumulator proof pub := by
  let proof : Slice U8 := ⟨List.replicate 57607 0#u8,by simp only [List.length_replicate]; scalar_tac⟩
  let pub : Slice U8 := ⟨List.replicate 1880 0#u8,by simp only [List.length_replicate]; scalar_tac⟩
  have zero : Port4C_QueryArithmetic.CanonE zeroE := by
    change ((0 : Nat) < 2147483647 ∧ 0 < 2147483647 ∧ 0 < 2147483647 ∧ 0 < 2147483647) ∧
      ((0 : Nat) < 2147483647 ∧ 0 < 2147483647 ∧ 0 < 2147483647 ∧ 0 < 2147483647)
    decide
  refine ⟨proof,pub,⟨rfl,?_,rfl,zero,zero,?_,zero,zero,?_,?_⟩⟩
  · simp only [accumulator,List.length_replicate]
  · intro x member
    change x ∈ List.replicate 2 zeroE at member
    obtain ⟨_,same⟩ := List.mem_replicate.mp member
    simpa only [same] using zero
  · exact List.length_replicate
  · exact List.length_replicate

/-- Consistency of the exact newly installed D188 association, not an actual
joint native accepted-pair fixture or a source adoption assertion. -/
theorem extraction_satisfiable {CoreError : Type} (adapterOps : AdapterRw.Ops) (ops : AspisR1CurrentCaller.Ops)
    (reserved : Bool) (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (std : ClaimsUnrolledFinish.StdCalls)
    (hashv : S2Z.Oracle.Parts → Result S2Z.Oracle.Digest) :
    ∃ native1 native2, S2W_DigestExtraction.AeneasExtraction
      (ClaimsUnrolledSdk.sdkOps {adapterOps with op43 := S2W_DigestExtraction.digest hashv}
        (WAdm_SameCut.dictionary ops reserved query geo) B std) native1 native2 hashv :=
  Op4P_Audit.extraction_satisfiable adapterOps (WAdm_Execution.base ops reserved query geo) B std hashv

#print axioms domain_nonempty
#print axioms extraction_satisfiable
end AspisR1.WAdm_Nonvacuity
end
