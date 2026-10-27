import JGb_Fixture
import JGj_PackedTwo
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_RealPackedTwo
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical)
open AspisR1PublicPreparation
/-- Partial SAME real-byte instance: successful leading/full packed calls on
JGb's actual gathered composition witnesses. Internal-pair and terminal
identification are not conclusions of this theorem. -/
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : FinishModel.Boundaries) (hash : Hash) :
    ∃ (selected : Array NQ 84#usize) (a b c : Array NQ 16#usize)
      (m : Array NQ 10#usize) (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
      (sops : state_only_poseidon.StateOnlyPoseidonSelectors)
      (leadingLow fullLow internalLow : NQ) (path : Array NQ 24#usize)
      (leading full : Array NQ 4#usize),
      array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy
        pool_v1.pair_forest_semantic_terminal.r0.Public.terminal_qm31.closure.Insts.CoreOpsFunctionFnMutTupleUsizeQM31
        field.QM31.ZERO JFu_TerminalCallback.claims=ok selected ∧
      pool_v1.pair_forest_semantic_terminal.composition_parts JFu_PublicSemantic.value selected
        JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
        JFu_TerminalPrefix.challenges.theta=JFy_CompositionTail.tail selected a b c m selectors sops leadingLow fullLow internalLow path ∧
      pool_v1.pair_forest_semantic_terminal.poseidon_selectors selectors=ok sops ∧
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected ⟨a,b,c⟩ sops=
        JFy_PoseidonPrefix.tail ⟨a,b,c⟩ sops leadingLow fullLow internalLow ∧
      canonical a ∧ canonical b ∧ canonical c ∧ canonical sops.local ∧
      state_only_poseidon.leading_pair_packed ⟨a,b,c⟩=ok leading ∧
      state_only_poseidon.interpolated_full_pair_packed a sops.local=ok full ∧
      canonical leading ∧ canonical full := by
  obtain ⟨expanded,y1,pre,view,claims,cs,mask,selected,a,b,c,m,selectors,sops,leading,full,internal,schedule,path,bits,sem,h1,copy,
    old,gather,validated,native,composition,hselected,hac,hbc,hcc,hmc,hs,hsh,hsl,hps,hpb,hpl,
    projected,hlc,hfc,hic,scheduled,hsc,pathed,hpc,semantic,bitcall,bitcanon,bitvalue,semcall,semcanon,semvalue,h1call,copycall,copycanon,activecanon,tail⟩ := JGb_Fixture.inhabited D B hash
  obtain ⟨lp,fp,rl,rf,cl,cf,_,_⟩ := JGj_PackedTwo.source ⟨a,b,c⟩ sops hac hcc hpl
  exact ⟨selected,a,b,c,m,selectors,sops,leading,full,internal,path,lp,fp,gather,composition,hps,projected,hac,hbc,hcc,hpl,rl,rf,cl,cf⟩
#print axioms source
end AspisR1.JGj_RealPackedTwo
end
