import S1AcceptedRoundsNumericV1
import S1SemanticFinishBoundsV1
import S1SemanticInstallationV1
set_option autoImplicit false
namespace AspisS1AcceptedRoundsNumeric
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open SemanticRoundsCheckedTrace

/-- Full four-word ranges on the exact returned alpha/extra/before_z1 arrays.
Claims, terminal, challenges and native source interpretation are not hidden
inside this predicate and are not asserted here. -/
def VerifiedNumeric {H : Type} (out : r1_semantic.Verified H) : Prop :=
  (∀ q ∈ out.alpha.val, Canonical q) ∧
  (∀ q ∈ out.extra.val, Canonical q) ∧
  (∀ q ∈ out.before_z1.val, Canonical q)

/-- Same complete finish supplies all producer calls. Its claims/terminal
implementations remain arbitrary, without any added numeric assumptions. -/
theorem accepted_finish_numeric {H : Type} (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pre : r1_wire.Prefix) (before : r1_wire.SemanticTranscript H)
    (challenges : r1_wire.Challenges) (obs : Option (verifier.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (accepted : FinishModel.finish children B D pub pre before challenges obs = ok (.Ok out)) :
    VerifiedNumeric out ∧ ∃ running after record initialArray initial,
      RoundModel.rounds children D pre before = ok (.Ok (running,out.alpha,after)) ∧
      r1_wire.Prefix.validated_record pre 14#u8 = ok (.Ok record) ∧
      children.decode 1#usize record 0#usize = ok (.Ok initialArray) ∧
      Array.index_usize initialArray 0#usize = ok initial ∧
      NumericRun D pre schedule
        (initial,Array.repeat 10#usize aspis_core.field.QM31.ZERO,before) (running,out.alpha,after) ∧
      Canonical running := by
  obtain ⟨running,t25,record25,record26,z0,t26,z1,t27,rounds,
    challengesEq,stateEq,transcriptEq,claimsCall,record25Call,extraCall,
    circle0,record26Call,beforeZ1Call,circle1,zEq⟩ :=
    S1SemanticFinishBounds.finish_success children B D pub pre before challenges obs out accepted
  obtain ⟨record,initialArray,initial,recordCall,decodeCall,indexCall,numeric,runningCanon,alphaCanon⟩ :=
    accepted_rounds_numeric D pre before t25 running out.alpha rounds
  refine ⟨⟨?_,decoded_members_canonical _ record25 87#usize out.extra extraCall,
    decoded_members_canonical _ record26 0#usize out.before_z1 beforeZ1Call⟩,
    running,t25,record,initialArray,initial,rounds,recordCall,decodeCall,indexCall,numeric,runningCanon⟩
  intro q member
  obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp member
  subst q
  exact alphaCanon ⟨i,by simpa [out.alpha.property] using hi⟩

/-- The actual source verifier return supplies its prefix/begin/finish; no
separately successful source child is an enclosing premise. -/
theorem accepted_verify_numeric {H : Type} (B : FinishModel.Boundaries)
    (D : aspis_core.Digest32 H) (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (out : r1_semantic.Verified H)
    (accepted : VerifyPrefix.verify (FinishModel.finish children B) D pub bytes hash obs = ok (.Ok out)) :
    VerifiedNumeric out := by
  obtain ⟨pre,initial,after,challenges,parsed,publicInit,begin,finish⟩ :=
    S1SemanticVerify.verify_success _ D pub bytes hash obs out accepted
  exact (accepted_finish_numeric B D pub pre after challenges obs out finish).1

/-- Complete field-preserving current semantic carrier, including every alpha,
extra and before_z1 coordinate. This is not a simplified semantic replacement. -/
def CurrentVerifiedNumeric {H : Type} (out : AspisR1CurrentCaller.r1_semantic.Verified H) : Prop :=
  VerifiedNumeric (AspisR1CurrentCaller.InstalledPreparation.retainedSem out)

theorem installed_verify_numeric {H : Type} (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (out : AspisR1CurrentCaller.r1_semantic.Verified H)
    (accepted : AspisR1CurrentCaller.S1SemanticInstallation.verify children B D pub bytes hash = ok (.Ok out)) :
    CurrentVerifiedNumeric out := by
  have source := AspisR1CurrentCaller.S1SemanticInstallation.verify_return children B D pub bytes hash out accepted
  exact accepted_verify_numeric (S1SemanticRootCopy.install B)
    (AspisR1CurrentCaller.InstalledPreparation.retainedDigest D)
    (AspisR1CurrentCaller.FirstComposition.toRetainedPublic pub) bytes hash none _ source

#print axioms accepted_finish_numeric
#print axioms accepted_verify_numeric
#print axioms installed_verify_numeric
end AspisS1AcceptedRoundsNumeric
