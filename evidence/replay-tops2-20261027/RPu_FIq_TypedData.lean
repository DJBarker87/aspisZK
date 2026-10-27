import RPu_FIq_SemanticSource
import RPu_FIq_TypedInitial
import RPu_FIq_TypedPolynomials
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIq_TypedData
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1CurrentCaller.InstalledPreparation
open RawActualAnnotatedPolynomialRun
theorem verified {H : Type} (B : FinishModel.Boundaries)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H)
    (pub : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (bytes : Slice U8) (hash : H) (sem : AspisR1CurrentCaller.r1_semantic.Verified H)
    (success : AspisR1CurrentCaller.S1SemanticInstallation.verify
      AspisS1ExtractedRoundChildren.children B D pub bytes hash=ok (.Ok sem)) :
    ∃ (pre : r1_wire.Prefix) (before after : r1_wire.SemanticTranscript H)
      (running : aspis_core.field.QM31) (record : r1_wire.ValidatedRecord)
      (decoded : Array aspis_core.field.QM31 1#usize) (initial : aspis_core.field.QM31)
      (entries : List (RoundEvidence (retainedDigest D) pre))
      (values : SemanticPrefixCodec.Full),
      PrefixAdapter.parseAccepted bytes=ok (.Ok pre) ∧
      RoundModel.rounds AspisS1ExtractedRoundChildren.children (retainedDigest D) pre before=
        ok (.Ok (running,(retainedSem sem).alpha,after)) ∧
      r1_wire.Prefix.validated_record pre 14#u8=ok (.Ok record) ∧
      AspisS1ExtractedRoundChildren.decodeMain 1#usize record 0#usize=ok (.Ok decoded) ∧
      Array.index_usize decoded 0#usize=ok initial ∧
      AnnotatedRun (retainedDigest D) pre SemanticRoundsCheckedTrace.schedule
        (initial,Array.repeat 10#usize aspis_core.field.QM31.ZERO,before)
        (running,(retainedSem sem).alpha,after) entries ∧
      entries.map RoundEvidence.q=(retainedSem sem).alpha.val ∧
      SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre ∧
      algebraMap ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact
        (DecodeMain initial)=SemanticPayloadView.claimAt14 values ∧
      (∀ (entry : RoundEvidence (retainedDigest D) pre) (mem : entry ∈ entries),
        (polynomialOf entry.coefficients).map
          (algebraMap ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact)=
          SemanticCoefficientCodec.polynomial
            (SemanticPayloadView.coeffAt values
              ⟨entry.round.val % 10,Nat.mod_lt _ (by decide)⟩)) ∧
      RawGenericPolynomialSumcheckChain.Chain (DecodeMain initial) (DecodeMain running)
        (entries.map (pairOf (retainedDigest D) pre)) := by
  obtain ⟨pre,before,after,running,record,decoded,initial,entries,parsed,rounds,
    read,decode,index,annotated,alpha,chain⟩ := FIq_SemanticSource.verified B D pub bytes hash sem success
  obtain ⟨values,typed,full,decodeFull⟩ := PrefixAdapter.parse_typedFull bytes pre parsed
  refine ⟨pre,before,after,running,record,decoded,initial,entries,values,
    parsed,rounds,read,decode,index,annotated,alpha,full,
    FIq_TypedInitial.initial pre record read decoded initial decode index values full,?_,chain⟩
  intro entry mem
  have exactValue := FIq_TypedPolynomials.same_entry bytes pre values full
    (retainedDigest D) _ _ entries annotated entry mem
  have bound := RawActualAnnotatedTypedRows.entry_schedule_round_lt annotated entry mem
  simpa only [Nat.mod_eq_of_lt bound] using exactValue

#print axioms verified
end AspisR1.FIq_TypedData
end
