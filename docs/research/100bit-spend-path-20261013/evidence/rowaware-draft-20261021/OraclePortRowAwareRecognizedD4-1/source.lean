import OraclePortRowAwareWalkD3

/-! Finite, fully cached row-zero history for the frozen node overlap.
Unlike the older witness, this table has no leaf answer equal to iv. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowAwareRecognizedD4
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalAddressEmbedding OracleDecisionMultiDecoder
open OraclePortRowAwareCausalD1

open OraclePortRowAwareWitnessD2
open OraclePortRowAwareWalkD3
attribute [local irreducible] support RawBoundedTrace.table InitialWalk.walk InitialPublicWalk.walk

theorem support_recognized : RecordedBinaryExperimentBin.dec node support ≠ none := by
  have habs : parseAbsorb nodeAddr = some (endpoint,p.lbl 1,p.enc m1) :=
    parseAbsorb_absorbA p endpoint (p.lbl 1) (p.enc m1) (p.encLen m1)
  have hc : CanonicalByteAddress.Canonical nodeAddr := by
    unfold nodeAddr absorbA; apply CanonicalByteAddress.canonical_ofBytes
  have hbytes : nodeAddr.toBytes = node := by
    simp only [nodeAddr,absorbA,Addr.toBytes_ofBytes,absorb]
    exact node_absorb.symm
  have hrow : UnifiedLabels.row (p.lbl 1) = 1 := by decide
  have hpub : RawFullPublicSelection.select node support = some pub := by
    rw [← hbytes]
    change RawPublicSelectionLift.select L (FullPublicSelection.select p)
      (toBytes (⟨nodeAddr,hc⟩ : AddrC L)) support = _
    rw [RawPublicSelectionLift.of_canonical]
    simp only [FullPublicSelection.select,habs,hrow]
    simp only [show 1 ≤ 26 from by decide,if_true,SemanticPublicSelection.select,
      support_walks.1,Option.map_some]
  have hctx : UnifiedSemanticContext.parse p pub.pubBytes nodeAddr
      (RawBoundedTrace.table L support) = some ⟨zero,records,m1⟩ := by
    apply UnifiedSemanticContext.parse_of_checks p _ _ _ endpoint _ _ zero records m1 habs
    · simp only [UnifiedSemanticRecovery.typed,support_walks.2,Option.bind_some,
        RawRoundDecode.decode_encode,Option.map_some]
    · exact IndexedMessage.read_encoded p 1 m1
  have hi : PublicInitParse.parse pub.pubBytes nodeAddr = none :=
    PublicInitAbsorbSeparation.parse_init_absorb_none p _ _ _ _ _
  rw [← hbytes]
  exact OracleDecisionMultiDecoderLift.semantic_recognizes pub ⟨nodeAddr,hc⟩ support
    endpoint (p.lbl 1) (p.enc m1) ⟨zero,records,m1⟩
    (by simpa only [toBytes,hbytes] using hpub) hi habs hrow hctx (by decide) (by decide)

#print axioms support_recognized
end AspisR1.OraclePortRowAwareRecognizedD4
end
