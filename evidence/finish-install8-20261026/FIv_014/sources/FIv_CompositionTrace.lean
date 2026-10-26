import FIv_Arithmetic
import FIq_Native14
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_CompositionTrace
open Aeneas Aeneas.Std Result FIq_Native
abbrev NQ := field.QM31
abbrev SemPub := pool_v1.pair_forest_semantic_terminal.SemanticPublic
abbrev composition := pool_v1.pair_forest_semantic_terminal.composition_parts

theorem reached (pub : SemPub) (claims : Array NQ 84#usize) (point : Array NQ 10#usize)
    (lambda chi theta comp g h active : NQ) (c1 : Array NQ 16#usize) (mask : Array NQ 10#usize)
    (success : composition pub claims point lambda chi theta=ok (.Ok (comp,c1,mask,g,h,active))) :
    ∃ (semantic : Array NQ 24#usize) (poseidon : Array NQ 4#usize)
      (prepared : field.PreparedQm31Multiplier) (middle : NQ)
      (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1)
      (iterator : core.iter.adapters.rev.Rev (FIq_Native.core.array.iter.IntoIter NQ 24#usize))
      (iterator1 : core.iter.adapters.rev.Rev (FIq_Native.core.array.iter.IntoIter NQ 4#usize)),
      field.PreparedQm31Multiplier.new theta=ok prepared ∧
      iterator.iter=semantic.val ∧ iterator1.iter=poseidon.val ∧
      pool_v1.pair_forest_semantic_terminal.composition_parts_loop0 iterator prepared copy.residual=ok middle ∧
      pool_v1.pair_forest_semantic_terminal.composition_parts_loop1 iterator1 prepared middle=ok comp ∧
      copy.active=active := by
  unfold composition pool_v1.pair_forest_semantic_terminal.composition_parts at success
  obtain ⟨⟨amount,invalid⟩,amountCall,success⟩ := FIv_Map.bind_success _ _ _ success
  cases invalid with
  | true => cases success
  | false =>
    obtain ⟨validated,validation,success⟩ := FIv_Map.bind_success _ _ _ success
    cases validated with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at success
      cases success
    | Ok unit =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at success
      obtain ⟨a,ha,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨a1,ha1,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨a2,ha2,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨maskOnly,hm,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨selectors,hs,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨sops,hsp,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨poseidon,hp,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨semantic,hsem,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨column,hcol,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨h1,hh1,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨variant,hv,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨copy,hcopy,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨prepared,hprep,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨iterator,hi,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨reverse,hr,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨middle,hmid,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨iterator1,hi1,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨reverse1,hr1,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨final,hfinal,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨gColumn,hgc,success⟩ := FIv_Map.bind_success _ _ _ success
      obtain ⟨gValue,hg,success⟩ := FIv_Map.bind_success _ _ _ success
      have output := core.result.Result.Ok.inj (Result.ok.inj success)
      have compSame := congrArg (fun p : NQ × Array NQ 16#usize × Array NQ 10#usize × NQ × NQ × NQ=>p.1) output
      have activeSame := congrArg (fun p : NQ × Array NQ 16#usize × Array NQ 10#usize × NQ × NQ × NQ=>p.2.2.2.2.2) output
      dsimp only at compSame activeSame
      have iterSame : reverse.iter=semantic.val := by
        cases Result.ok.inj hr
        cases Result.ok.inj hi
        rfl
      have iterSame1 : reverse1.iter=poseidon.val := by
        cases Result.ok.inj hr1
        cases Result.ok.inj hi1
        rfl
      exact ⟨semantic,poseidon,prepared,middle,copy,reverse,reverse1,hprep,iterSame,iterSame1,hmid,
        by rw [← compSame];exact hfinal,activeSame⟩

#print axioms reached
end AspisR1.FIv_CompositionTrace
end
