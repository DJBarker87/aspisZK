import JGl_TerminalSuccess
import FJh_InternalOnRun
import JGl_SelectedCells
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGl_InternalSameRun
open Aeneas Aeneas.Std Result FIq_Native
open FIw_ArrayValue (canonical decoded)
/-- Both the internal VALUE and its call are obtained from JGb's SAME
retained-byte evaluator return. No independent successful run is supplied. -/
theorem inhabited {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (hash : H) :
    ∃ (selected : Array field.QM31 84#usize) (a b c : Array field.QM31 16#usize)
      (s : state_only_poseidon.StateOnlyPoseidonSelectors)
      (pos : Array field.QM31 4#usize) (internal : Array field.QM31 16#usize),
      array_from_fn_copy 84#usize field.QM31.Insts.CoreMarkerCopy JGl_SelectedCells.builder
        field.QM31.ZERO JFu_TerminalCallback.claims=ok selected ∧
      state_only_poseidon.evaluate_state_only_poseidon_oracle_projected ⟨a,b,c⟩ s=ok pos ∧
      state_only_poseidon.interpolated_internal_pair a s.local=ok internal ∧
      canonical internal ∧ decoded internal=R0P.poseidonInterpolatedInternalPair (decoded a) (decoded s.local) := by
  obtain ⟨selected,a,b,c,m,s,sops,sem,pos,comp,g,h,copy,out,
    gather,hs,ha,hb,hc,hl,block,sel,ps,runpos,cpos,vpos,runsem,csem,vsem,runh,runcopy,
    runcomp,ccomp,cg,vcomp,run,cout,vout⟩ := JGl_TerminalSuccess.source D B hash
  obtain ⟨internal,ri,ci,vi⟩ := FJh_InternalOnRun.value ⟨a,b,c⟩ sops pos ha hl runpos
  exact ⟨selected,a,b,c,sops,pos,internal,gather,runpos,ri,ci,vi⟩
#print axioms inhabited
end AspisR1.JGl_InternalSameRun
end
