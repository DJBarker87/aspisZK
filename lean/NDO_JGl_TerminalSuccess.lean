import NDO_JGl_RealFixture
import NDO_JGd_MainInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_TerminalSuccess
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeValue (Canon decode)
open FIw_ArrayValue (canonical decoded)
/-- Unconditional actual public terminal success on retained bytes, with the
original native value formula. No numeric identification is asserted. -/
theorem source {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (hash : H) :
    ∃ (selected : Array field.QM31 84#usize) (a b c : Array field.QM31 16#usize)
      (m : Array field.QM31 10#usize) (s : pool_v1.pair_forest_copy_terminal.Selectors)
      (sops : state_only_poseidon.StateOnlyPoseidonSelectors)
      (sem : Array field.QM31 24#usize) (pos : Array field.QM31 4#usize)
      (comp g h : field.QM31)
      (copy : pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledCopyTerminalV1)
      (out : field.QM31),
      array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
        pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO JFu_TerminalCallback.claims=ok selected ∧
      canonical selected ∧ canonical a ∧ canonical b ∧ canonical c ∧ canonical sops.local ∧ Canon sops.block ∧
      pool_v1.pair_forest_copy_terminal.Selectors.boxed_at_point JFu_TerminalPrefix.alpha=ok s ∧
      pool_v1.pair_forest_semantic_terminal.poseidon_selectors s=ok sops ∧
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected ⟨a,b,c⟩ sops=ok pos ∧
      canonical pos ∧ decoded pos=FJh_Native07RawValue.model ⟨a,b,c⟩ sops ∧
      pool_v1.pair_forest_semantic_terminal.semantic_packed JFu_PublicSemantic.value ⟨a,b,c⟩ s=ok sem ∧
      canonical sem ∧ decoded sem=FIy_NativeCoefficients.model JFu_PublicSemantic.value ⟨a,b,c⟩ s ∧
      pool_v1.pair_forest_semantic_terminal.selected_claim selected 0#usize 26#usize=ok h ∧
      pool_v1.pair_forest_copy_terminal.evaluate_with_selectors a h s
        JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
        JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index .PrivateTransfer=ok copy ∧
      pool_v1.pair_forest_semantic_terminal.composition_parts JFu_PublicSemantic.value selected
        JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
        JFu_TerminalPrefix.challenges.theta=ok (.Ok (comp,a,m,g,h,copy.active)) ∧
      Canon comp ∧ Canon g ∧ decode comp=FIv_CompositionValue.polynomial
        (decode JFu_TerminalPrefix.challenges.theta) sem pos copy.residual ∧
      pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31
        (FIq_Carriers.toPublic JFs_PublicSerialization.value) JFu_TerminalCallback.claims
        JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges=ok (.Ok out) ∧
      Canon out ∧ decode out=FIv_TerminalValue.formula
        (FIv_EqualityValue.weight JFu_TerminalPrefix.challenges.zc JFu_TerminalPrefix.alpha)
        (decode comp) (decode JFu_TerminalPrefix.challenges.mu) (decode h) (decode copy.active) := by
  obtain ⟨expanded,y1,pre,view,claims,cs,mask,selected,a,b,c,m,s,sops,l,f,i,schedule,path,bits,sem,h,copy,
    old,gather,validated,native,composition,hselected,hac,hbc,hcc,hmc,hs,hsh,hsl,hps,hpb,hpl,
    projected,hlc,hfc,hic,scheduled,hsc,pathed,hpc,semantic,bitcall,bitcanon,bitvalue,semcall,semcanon,semvalue,hcall,copycall,copycanon,activecanon,
    pos,comp,g,out,poscall,poscanon,compcall,compcanon,gcanon,compvalue,outcall,outcanon,outvalue⟩ :=
    JGl_RealFixture.inhabited D B hash
  have run := projected.trans poscall
  have val := FJh_Native07RawValue.value ⟨a,b,c⟩ sops pos hac hbc hcc hpl hpb run
  exact ⟨selected,a,b,c,m,s,sops,sem,pos,comp,g,h,copy,out,gather,hselected,hac,hbc,hcc,hpl,hpb,
    hs,hps,run,poscanon,val.2,semcall,semcanon,semvalue,hcall,copycall,compcall,compcanon,gcanon,compvalue,outcall,outcanon,outvalue⟩
#print axioms source

end AspisR1.JGl_TerminalSuccess
end
