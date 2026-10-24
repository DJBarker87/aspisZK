import S1FinishChildrenV1
import S1FinishSelectorsV1
import S1SemanticFinishMaskCallsV1
set_option autoImplicit false
namespace AspisS1FinishChildren
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation
open AspisS1ExtractedRoundChildren (MainQM)

/-- Same accepted full finish: both mask input arrays have the exact source
columns of its returned claims, and all mask/arithmetic calls belong to this
execution. No separate selector, terminal, mask or arithmetic success is a
premise. Claims/terminal implementations remain explicit source interfaces. -/
theorem finish_mask_provenance (claims : Claims) (terminal : Terminal)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (pre : r1_wire.Prefix)
    (before : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (out : r1_semantic.Verified H)
    (accepted : FinishModel.finish AspisS1ExtractedRoundChildren.children
      (install claims terminal) D pub pre before challenges none = ok (.Ok out)) :
    ∃ (running : MainQM) (afterRounds : r1_wire.SemanticTranscript H)
      (first : Array MainQM 16#usize) (second : Array MainQM 10#usize)
      (row0 : Array MainQM 29#usize)
      (g maskValue terminalValue product sum extra28 maskedTerminal : MainQM),
      RoundModel.rounds AspisS1ExtractedRoundChildren.children D pre before =
        ok (.Ok (running,out.alpha,afterRounds)) ∧
      claims pre = ok (.Ok out.claims) ∧
      terminal pub out.claims out.alpha challenges = ok (.Ok terminalValue) ∧
      AspisR1SelectedMaskProbe.core.array.from_fn 16#usize (FinishModel.closureFn9 D) out.claims = ok first ∧
      first.val = (List.range 16).map (AspisS1FinishSelectors.cell out.claims) ∧
      AspisR1SelectedMaskProbe.core.array.from_fn 10#usize (FinishModel.closureFn5 D) out.claims = ok second ∧
      second.val = (List.range 10).map (fun i => AspisS1FinishSelectors.cell out.claims (16+i)) ∧
      Array.index_usize out.claims 0#usize = ok row0 ∧
      Array.index_usize row0 27#usize = ok g ∧
      mask first second g out.alpha = ok maskValue ∧
      mul challenges.eta terminalValue = ok product ∧
      add maskValue product = ok sum ∧
      Array.index_usize out.extra 28#usize = ok extra28 ∧
      add sum extra28 = ok maskedTerminal ∧
      core.cmp.PartialEq.ne.trait_default
        aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running maskedTerminal = ok false := by
  obtain ⟨running,t25,r25,r26,z0,t26,z1,t27,hrounds,_,_,_,hclaims,_,_,_,_,_,_,_,
    first,second,row0,g,maskValue,terminalValue,product,sum,extra28,maskedTerminal,
    hterminal,hfirst,hsecond,hrow,hg,hmask,hproduct,hsum,hextra,hfinal,hguard⟩ :=
    S1SemanticFinishMaskCalls.finish_success AspisS1ExtractedRoundChildren.children
      (install claims terminal) D pub pre before challenges none out accepted
  change AspisR1SelectedMaskProbe.core.array.from_fn 16#usize (FinishModel.closureFn9 D) out.claims = ok first at hfirst
  change AspisR1SelectedMaskProbe.core.array.from_fn 10#usize (FinishModel.closureFn5 D) out.claims = ok second at hsecond
  obtain ⟨firstModel,firstCall,firstValues⟩ := AspisS1FinishSelectors.first_total D out.claims
  obtain ⟨secondModel,secondCall,secondValues⟩ := AspisS1FinishSelectors.second_total D out.claims
  have firstEq : first = firstModel := Result.ok.inj (hfirst.symm.trans firstCall)
  have secondEq : second = secondModel := Result.ok.inj (hsecond.symm.trans secondCall)
  have firstContents := (congrArg (fun a : Array MainQM 16#usize => a.val) firstEq).trans firstValues
  have secondContents := (congrArg (fun a : Array MainQM 10#usize => a.val) secondEq).trans secondValues
  exact ⟨running,t25,first,second,row0,g,maskValue,terminalValue,product,sum,extra28,maskedTerminal,
    hrounds,hclaims,hterminal,hfirst,firstContents,hsecond,secondContents,hrow,hg,hmask,hproduct,hsum,hextra,hfinal,hguard⟩

#print axioms finish_mask_provenance
end AspisS1FinishChildren
