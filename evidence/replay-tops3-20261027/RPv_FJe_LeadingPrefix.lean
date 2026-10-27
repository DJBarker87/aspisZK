import RPv_FJb_LeadingOnRun
import RPv_FJb_InitialConstants
import RPv_FJb_M31LazyRound
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJe_LeadingPrefix
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open FJa_PoseidonOrigins (Openings)
def absorbed (o : Openings) := fun j : Fin (16#usize).val=>
  if j.val<8 then decoded o.z j+decoded o.xor12_z j else decoded o.z j
/-- Compose the imported original absorption/linear/first-round values on the
same successful leading call. The final packed call remains explicit. -/
theorem value (o : Openings) (out : Array NQ 4#usize)
    (hz : canonical o.z) (hx : canonical o.xor12_z)
    (run : state_only_poseidon.leading_pair_packed o=ok out) :
    ∃ middle : Array NQ 16#usize,canonical middle ∧
      decoded middle=R0P.poseidonFullRound (R0P.poseidonExternalLinear (absorbed o))
        (R0P.poseidonExternalInitial 0) ∧
      state_only_poseidon.full_round_m31_constants_packed middle
        (FJb_InitialConstants.row 1)=ok out := by
  obtain ⟨a,initial,middle,c0,c1,_,ca,va,hi,hc0,hm,hc1,tail⟩ :=
    FJb_LeadingOnRun.value o out hz hx run
  have e0 : c0=FJb_InitialConstants.row 0 :=
    Result.ok.inj (hc0.symm.trans (FJb_InitialConstants.read 0#usize (by decide)))
  have e1 : c1=FJb_InitialConstants.row 1 :=
    Result.ok.inj (hc1.symm.trans (FJb_InitialConstants.read 1#usize (by decide)))
  subst c0
  subst c1
  have vi := FJb_ExternalExact.value a initial ca hi
  have vm := FJb_M31LazyRound.value initial middle (FJb_InitialConstants.row 0)
    vi.1 (FJb_InitialConstants.bounded 0) hm
  have ea : decoded a=absorbed o := funext va
  have ec : (fun j : Fin (16#usize).val=>
      ((FJb_TailCell.cell (FJb_InitialConstants.row 0) j).val : FIv_NativeValue.K))=
      R0P.poseidonExternalInitial 0 := funext (FJb_InitialConstants.model 0)
  refine ⟨middle,vm.1,?_,tail⟩
  exact vm.2.trans (congrArg₂ R0P.poseidonFullRound
    (vi.2.trans (congrArg R0P.poseidonExternalLinear ea)) ec)
#print axioms value
end AspisR1.FJe_LeadingPrefix
end
