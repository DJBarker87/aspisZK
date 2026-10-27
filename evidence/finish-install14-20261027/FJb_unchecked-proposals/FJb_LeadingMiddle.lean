import FJb_InitialConstants
import FJb_M31LazyRound
import FJb_LeadingOnRun
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJb_LeadingMiddle
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings)
open FJb_MatrixGroupStep (State)
def absorbed (o : Openings) (j : Fin (16#usize).val) : K :=
  if j.val < 8 then decoded o.z j+decoded o.xor12_z j else decoded o.z j
/-- Complete VALUE through the actual leading absorption,external layer and
first M31 round. The final packed call remains the SAME reached native call. -/
theorem value (o : Openings) (out : Array NQ 4#usize)
    (hz : canonical o.z) (hx : canonical o.xor12_z)
    (run : state_only_poseidon.leading_pair_packed o=ok out) :
    ∃ middle : State,canonical middle ∧
      decoded middle=R0P.poseidonFullRound
        (R0P.poseidonExternalLinear (absorbed o)) (R0P.poseidonExternalInitial 0) ∧
      state_only_poseidon.full_round_m31_constants_packed middle (FJb_InitialConstants.row 1)=ok out := by
  obtain ⟨a,initial,middle,c0,c1,ha,hca,va,hi,rc0,hm,rc1,hfinal⟩ :=
    FJb_LeadingOnRun.value o out hz hx run
  have ec0 : c0=FJb_InitialConstants.row 0 :=
    Result.ok.inj (rc0.symm.trans (FJb_InitialConstants.read 0#usize (by decide)))
  have ec1 : c1=FJb_InitialConstants.row 1 :=
    Result.ok.inj (rc1.symm.trans (FJb_InitialConstants.read 1#usize (by decide)))
  subst c0
  subst c1
  have ve := FJb_ExternalExact.value a initial hca hi
  have vm := FJb_M31LazyRound.value initial middle (FJb_InitialConstants.row 0)
    ve.1 (FJb_InitialConstants.bounded 0) hm
  have ae : decoded a=absorbed o := by funext j;exact va j
  have ie : decoded initial=R0P.poseidonExternalLinear (absorbed o) :=
    ve.2.trans (congrArg R0P.poseidonExternalLinear ae)
  have ce : (fun j=>((FJb_TailCell.cell (FJb_InitialConstants.row 0) j).val : K))=
      R0P.poseidonExternalInitial 0 := by
    funext j
    exact FJb_InitialConstants.model 0 j
  exact ⟨middle,vm.1,vm.2.trans (congrArg₂ R0P.poseidonFullRound ie ce),hfinal⟩
#print axioms value
end AspisR1.FJb_LeadingMiddle
end
