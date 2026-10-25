import S1ReachedFinalNumericV1
import S1AcceptedChallengesNumericV1
set_option autoImplicit false
namespace AspisS1ReachedFinalEtaNumeric
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisR1ClaimPreparedBridge AspisS1ExtractedRoundChildren
open AspisS1SourceFinalOps (add mul decodeQ)

/-- Same source-call witnesses and exact additive equation. Eta canonicality
is established; only the retained terminal domain remains on the product formula. -/
def ReachedFinalEtaNumeric {H : Type} (base : FinishModel.Boundaries)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (sem : r1_semantic.Verified H) : Prop :=
  ∃ (first : Array MainQM 16#usize) (second : Array MainQM 10#usize)
    (row0 : Array MainQM 29#usize) (g maskValue terminalValue product sum extra28 target running : MainQM),
    AspisR1SelectedMaskProbe.core.array.from_fn 16#usize (FinishModel.closureFn9 D) sem.claims=ok first ∧
    AspisR1SelectedMaskProbe.core.array.from_fn 10#usize (FinishModel.closureFn5 D) sem.claims=ok second ∧
    Array.index_usize sem.claims 0#usize=ok row0 ∧ Array.index_usize row0 27#usize=ok g ∧
    AspisS1SourceMaskOps.mask first second g sem.alpha=ok maskValue ∧
    base.terminal pub sem.claims sem.alpha sem.challenges=ok (.Ok terminalValue) ∧
    mul sem.challenges.eta terminalValue=ok product ∧ add maskValue product=ok sum ∧
    Array.index_usize sem.extra 28#usize=ok extra28 ∧ add sum extra28=ok target ∧
    core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 running target=ok false ∧
    Canonical maskValue ∧ Canonical product ∧ Canonical sum ∧ Canonical extra28 ∧ Canonical target ∧
    decodeQ target=decodeQ maskValue+decodeQ product+decodeQ extra28 ∧
    Canonical sem.challenges.eta ∧ (Canonical terminalValue →
      decodeQ target=decodeQ maskValue+decodeQ sem.challenges.eta*decodeQ terminalValue+decodeQ extra28)


theorem of_reached {H : Type} (base : FinishModel.Boundaries)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (sem : r1_semantic.Verified H)
    (numeric : AspisS1ReachedFinalNumeric.ReachedFinalNumeric base D pub sem)
    (eta : Canonical sem.challenges.eta) : ReachedFinalEtaNumeric base D pub sem := by
  obtain ⟨first,second,row0,g,maskValue,terminalValue,product,sum,extra28,target,running,
    hfirst,hsecond,hrow,hg,hmask,hterminal,hproduct,hsum,hextra,hfinal,hguard,
    cmask,cproduct,csum,cextra,ctarget,additive,formula⟩ := numeric
  exact ⟨first,second,row0,g,maskValue,terminalValue,product,sum,extra28,target,running,
    hfirst,hsecond,hrow,hg,hmask,hterminal,hproduct,hsum,hextra,hfinal,hguard,
    cmask,cproduct,csum,cextra,ctarget,additive,eta,formula eta⟩

/-- Eta is from the SAME reached Verified record, not an added caller premise. -/
theorem of_current {H : Type} (base : FinishModel.Boundaries)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (numeric : AspisS1ReachedFinalNumeric.ReachedFinalNumeric base D pub
      (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem))
    (challenges : AspisS1SemanticArrayRanges.CurrentVerifiedChallengesNumeric sem) :
    ReachedFinalEtaNumeric base D pub (AspisR1CurrentCaller.InstalledPreparation.retainedSem sem) :=
  of_reached base D pub _ numeric challenges.2.2.2.2.1

#print axioms of_reached
#print axioms of_current
end AspisS1ReachedFinalEtaNumeric
