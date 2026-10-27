import JGx_SdkAfterValidationEq
import JGx_MagicGate
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHf_Stage2Inversion
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

theorem source (ops : Ops) (program : solana_pubkey.Pubkey)
    (accounts : S2W_ExtractionBoundary.Accounts) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot)
    (count : Slice.len accounts=7#usize)
    (magic : JGx_MagicGate.value ops data=ok false)
    (accepted : r1_pool_adapter.owned.stage2_owned ops program accounts data slot=ok (.Ok ())) :
    ∃ validated,r1_pool_adapter.owned.validate_asq8 ops program accounts data slot=ok (.Ok validated) := by
  unfold r1_pool_adapter.owned.stage2_owned at accepted
  rw [count] at accepted
  simp only [show (7#usize !=7#usize)=false from by decide,Bool.false_eq_true,ite_false] at accepted
  unfold JGx_MagicGate.value at magic
  obtain ⟨o,read,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ magic
  obtain ⟨s,index,neq⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  rw [read,bind_tc_ok,index,bind_tc_ok,neq,bind_tc_ok] at accepted
  simp only [Bool.false_eq_true,ite_false] at accepted
  cases call : r1_pool_adapter.owned.validate_asq8 ops program accounts data slot with
  | fail e=>simp only [call,bind_tc_fail] at accepted;cases accepted
  | div=>simp only [call,bind_tc_div] at accepted;cases accepted
  | ok result=>
    cases result with
    | Ok validated=>exact ⟨validated,rfl⟩
    | Err e=>
      simp only [call,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at accepted
      cases accepted
#print axioms source
end AspisR1.JHf_Stage2Inversion
end
