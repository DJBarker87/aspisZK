import FJf_PartialValue
import FJc_ArrayUpdateValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_PartialsCell
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)

theorem value (f : Slice U8) (common : Array NQ 16#usize) (hc : FJf_QMArray.canon common)
    (iter cursor : FIo_RangeNext.Range) (partials next : Array NE 4#usize)
    (he : iter.end.val=4) (hp : FIo_ArrayCanon.Holds partials)
    (run : FIo_Native.weights.shared_partials_loop.body f common iter partials=ok (.cont (cursor,next))) :
    cursor.end=iter.end ∧ cursor.start.val=iter.start.val+1 ∧ iter.start.val < iter.end.val ∧
    FIo_ArrayCanon.Holds next ∧
    ∀ s : Usize,FIp_ArrayValue.value next s.val=
      if iter.start.val=s.val then FJf_PartialCell.sumPrefix f common s 16 else FIp_ArrayValue.value partials s.val := by
  unfold FIo_Native.weights.shared_partials_loop.body at run
  obtain ⟨⟨o,cursor'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some s =>
    obtain ⟨r,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases r with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame,bind_tc_ok] at run
      cases run
    | Ok out =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨updated,hu,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases Result.ok.inj run
      have pr := FIo_RangeNext.some_next iter cursor s hn
      have hs : s.val < 4 := by rw [pr.1];omega
      have pv := FJf_PartialValue.sixteen f common s hs hc out hr
      refine ⟨pr.2.1,pr.2.2.1,pr.2.2.2,FIo_ArrayCanon.update partials updated s out hp pv.1 hu,?_⟩
      intro t
      rw [FJc_ArrayUpdateValue.value partials updated s out t.val hu,pr.1]
      by_cases eq : iter.start.val=t.val
      · rw [if_pos eq,if_pos eq,pv.2]
        have st : s=t := UScalar.eq_of_val_eq (by rw [pr.1];exact eq)
        rw [st]
      · rw [if_neg eq,if_neg eq]
#print axioms value
end AspisR1.FJg_PartialsCell
end
