import JGj_RealPackedTwo
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGj_RealPackedValues
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FIw_ArrayValue (canonical decoded)
open ExtractedMaskQmPackBase4Arithmetic (iBasis uBasis)
/-- The exact imported FJe values on JGb's SAME real-byte native operands. -/
theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries) (hash : Hash) :
    ∃ (selected : Array NQ 84#usize) (a b c : Array NQ 16#usize)
      (m : Array NQ 10#usize) (selectors : pool_v1.pair_forest_copy_terminal.Selectors)
      (sops : state_only_poseidon.StateOnlyPoseidonSelectors)
      (leadingLow fullLow internalLow : NQ) (path : Array NQ 24#usize)
      (leading full : Array NQ 4#usize),
      pool_v1.pair_forest_semantic_terminal.composition_parts JFu_PublicSemantic.value selected
        JFu_TerminalPrefix.alpha JFu_TerminalPrefix.challenges.lambda JFu_TerminalPrefix.challenges.chi
        JFu_TerminalPrefix.challenges.theta=JFy_CompositionTail.tail selected a b c m selectors sops leadingLow fullLow internalLow path ∧
      state_only_poseidon.leading_pair_packed ⟨a,b,c⟩=ok leading ∧
      state_only_poseidon.interpolated_full_pair_packed a sops.local=ok full ∧
      canonical leading ∧ canonical full ∧
      decoded leading=(fun g=>R0P.poseidonPackingFormula iBasis uBasis
        (fun j=>R0P.poseidonLeadingPair (decoded a) (decoded c) (FJe_ExternalAdjoint.lane g j))) ∧
      decoded full=(fun g=>R0P.poseidonPackingFormula iBasis uBasis
        (fun j=>R0P.poseidonInterpolatedFullPair (decoded a) (decoded sops.local) (FJe_ExternalAdjoint.lane g j))) := by
  obtain ⟨selected,a,b,c,m,selectors,sops,l,f,i,path,lp,fp,_,composition,_,_,ca,cb,cc,cs,rl,rf,cl,cf⟩ :=
    JGj_RealPackedTwo.source D B hash
  have vl := FJe_PackedValues.leading ⟨a,b,c⟩ lp ca cc rl
  have vf := FJe_PackedValues.full a sops.local fp ca cs rf
  exact ⟨selected,a,b,c,m,selectors,sops,l,f,i,path,lp,fp,composition,rl,rf,cl,cf,vl.2,vf.2⟩
#print axioms source
end AspisR1.JGj_RealPackedValues
end
