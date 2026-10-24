import S1TopPrepareCarrierV1
import S1ClosedPrepareProvenanceV1
set_option autoImplicit false
namespace AspisS1TopPrepareSource
open Aeneas Aeneas.Std Result
open AspisR1ClaimPreparedBridge AspisS1TopPrepareCarrier

/-- Same Copy and digest operations, with no hash/state carrier replacement. -/
def currentDigest {H : Type} (D : VTop_Stages.aspis_core.digest.Digest32 H) :
    AspisR1CurrentCaller.aspis_core.digest.Digest32 H :=
  {coremarkerCopyInst:=D.coremarkerCopyInst,digest:=D.digest}

def currentObserver (obs : Option (VTop_Stages.verifier.Phase → Result Unit)) :
    Option (AspisR1CurrentCaller.verifier.Phase → Result Unit) :=
  obs.map (fun observe => fun phase => observe (AspisS6CurrentVerifierCarrier.fromPhase phase))

/-- Complete current generated source prepare body at the top-stage ABI.
All Prepared and returned scratch fields, errors, fail/div and observer calls
are retained. This is a source-body installation candidate, not an assertion
that the remaining native child/SDK/runtime bindings are already established. -/
def prepare (ops : AspisR1CurrentCaller.Ops) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (obs : Option (VTop_Stages.verifier.Phase → Result Unit))
    (input : Array Top.E 29#usize) :
    Result (core.result.Result Top.Prepared VTop_Stages.verifier.Error × Array Top.E 29#usize) := do
  let (result,scratch) ← AspisR1CurrentCaller.verifier.candidate.prepare
    (AspisR1CurrentCaller.BorrowedClaimPrepared.closedInstall ops) (currentDigest D)
    (AspisS6CurrentVerifierCarrier.toPublic pub) proof hash (currentObserver obs) (mapArray fromE input)
  ok ((match result with
    | .Ok prepared => .Ok (toPrepared prepared)
    | .Err error => .Err (AspisS6CurrentVerifierCarrier.fromError error)),mapArray toE scratch)

def install (base : VTop_Stages.Ops) (ops : AspisR1CurrentCaller.Ops) : VTop_Stages.Ops :=
  {base with op7:=prepare ops}

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (success : (m >>= k)=ok out) : ∃ value,m=ok value ∧ k value=ok out := by
  cases m with
  | ok value => exact ⟨value,rfl,success⟩
  | fail error => cases success
  | div => cases success

/-- Actual same source-body return and FULL post-scratch, not an independent
success or a selected Prepared value chosen to fit the desired conclusion. -/
theorem prepare_return (ops : AspisR1CurrentCaller.Ops) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (success : prepare ops D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∃ (current : Current.Prepared) (g : Array Current.E 29#usize),
      AspisR1CurrentCaller.verifier.candidate.prepare
        (AspisR1CurrentCaller.BorrowedClaimPrepared.closedInstall ops) (currentDigest D)
        (AspisS6CurrentVerifierCarrier.toPublic pub) proof hash none (mapArray fromE input)=ok (.Ok current,g) ∧
      prepared=toPrepared current ∧ scratch=mapArray toE g := by
  unfold prepare at success
  obtain ⟨pair,source,returned⟩ := bind_success _ _ _ success
  rcases pair with ⟨result,g⟩
  cases result with
  | Err error => cases returned
  | Ok current =>
    have same := Result.ok.inj returned
    have preparedEq := core.result.Result.Ok.inj (congrArg Prod.fst same)
    exact ⟨current,g,source,preparedEq.symm,(congrArg Prod.snd same).symm⟩

/-- Concrete top-ABI prepare variant instance; no variant law is a premise. -/
theorem prepare_variant (ops : AspisR1CurrentCaller.Ops) {H : Type}
    (D : VTop_Stages.aspis_core.digest.Digest32 H)
    (pub : VTop_Stages.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (input scratch : Array Top.E 29#usize) (prepared : Top.Prepared)
    (success : prepare ops D pub proof hash none input=ok (.Ok prepared,scratch)) : prepared.variant=.S2 := by
  obtain ⟨current,g,source,equal,scratchEq⟩ := prepare_return ops D pub proof hash input scratch prepared success
  have variant := AspisR1CurrentCaller.BorrowedClaimPrepared.closed_prepare_variant
    ops (currentDigest D) _ proof hash current (mapArray fromE input) g source
  rw [equal]
  change toVariant current.variant=.S2
  rw [variant]
  rfl

#print axioms prepare_return
#print axioms prepare_variant
end AspisS1TopPrepareSource
