import OraclePortRowAwareCausalD1
import OracleDecisionMultiDecoder
import RawCutLiteralTranscriptSuccessor
import OraclePortFrameShapesC6

/-! Finite, fully cached row-zero history for the frozen node overlap.
Unlike the older witness, this table has no leaf answer equal to iv. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowAwareWitnessD2
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalAddressEmbedding OracleDecisionMultiDecoder
open OraclePortRowAwareCausalD1

def squeezed : Bytes := (squeezeA p absorbed).toBytes
def answer : State := fun _ => 5

def support : Table Bytes State := fun b =>
  if b = initial.toBytes then some s0 else
  if b = row0.toBytes then some absorbed else
  if b = advanced.toBytes then some endpoint else
  if b = squeezed then some answer else none

theorem support_fibers :
    (∀ b, support b = some s0 ↔ b = initial.toBytes) ∧
    (∀ b, support b = some absorbed ↔ b = row0.toBytes) ∧
    (∀ b, support b = some endpoint ↔ b = advanced.toBytes) := by
  have hl := byte_lengths
  have hs : squeezed.length = 33 := by
    simp [squeezed, squeezeA, Addr.toBytes_ofBytes, squeeze, bytes_length]
  have h01 : initial.toBytes ≠ row0.toBytes := by intro h; have := congrArg List.length h; omega
  have h02 : initial.toBytes ≠ advanced.toBytes := by intro h; have := congrArg List.length h; omega
  have h12 : row0.toBytes ≠ advanced.toBytes := by intro h; have := congrArg List.length h; omega
  have h0s : initial.toBytes ≠ squeezed := by intro h; have := congrArg List.length h; omega
  have h1s : row0.toBytes ≠ squeezed := by intro h; have := congrArg List.length h; omega
  have h2s : advanced.toBytes ≠ squeezed := by
    simp only [advanced, squeezed, advanceA, squeezeA, Addr.toBytes_ofBytes, advance, squeeze]
    simp
  have ha : answer ≠ s0 ∧ answer ≠ absorbed ∧ answer ≠ endpoint := by decide
  rcases state_distinct with ⟨hsa,hse,hsz,hae,haz,hez⟩
  refine ⟨?_,?_,?_⟩ <;> intro b <;> unfold support <;>
    split_ifs <;> simp_all only [Option.some.injEq, reduceCtorEq,
      Ne.symm hsa, Ne.symm hse, Ne.symm hae]

theorem support_walks :
    InitialPublicWalk.walk p (RawBoundedTrace.table L support) 27 endpoint =
      some ((pub,zero), RawRoundDecode.encode p 0 records) ∧
    InitialWalk.walk p pub.pubBytes (RawBoundedTrace.table L support) 27 endpoint =
      some (zero, RawRoundDecode.encode p 0 records) := by
  have fibers := And.intro
    (bounded_fiber support initial (CanonicalByteAddress.canonical_ofBytes _ _) s0 support_fibers.1)
    (And.intro
      (bounded_fiber support row0 (CanonicalByteAddress.canonical_ofBytes _ _) absorbed support_fibers.2.1)
      (bounded_fiber support advanced (CanonicalByteAddress.canonical_ofBytes _ _) endpoint support_fibers.2.2))
  have look0 : ReseedBoundary.findCell (RawBoundedTrace.table L support) s0 = some initial := by
    rw [ReseedBoundary.findCell,theUnique_eq_some]
    ext a
    simpa only [cellsWith,Finset.mem_filter,Finset.mem_univ,true_and,and_true,Finset.mem_singleton]
      using fibers.1 a
  have look1 : ReseedBoundary.findCell (RawBoundedTrace.table L support) absorbed = some row0 := by
    rw [ReseedBoundary.findCell,theUnique_eq_some]
    ext a
    simpa only [cellsWith,Finset.mem_filter,Finset.mem_univ,true_and,and_true,Finset.mem_singleton]
      using fibers.2.1 a
  have look2 : theUnique (advPre p (RawBoundedTrace.table L support) endpoint) = some absorbed := by
    rw [theUnique_eq_some]
    ext s
    simp only [advPre,preimages,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,fibers.2.2]
    exact ⟨fun h => advanceA_injective p h, fun h => congrArg (advanceA p) h⟩
  have hp : PublicInitParse.parse pub.pubBytes initial = some zero :=
    PublicInitParse.parse_addr [] (by decide) (by decide) zero
  have hr := RawPublicInitParser.of_fixed_parse pub initial zero rfl hp
  have hroot : InitialPublicWalk.rootAt (RawBoundedTrace.table L support) s0 = some (pub,zero) := by
    rw [InitialPublicWalk.rootAt,look0,Option.bind_some,hr]
  have hfroot : InitialWalk.rootAt pub.pubBytes (RawBoundedTrace.table L support) s0 = some zero := by
    rw [InitialWalk.rootAt,look0]; exact hp
  have ha : parseAbsorb row0 = some (s0,p.lbl 0,p.enc m0) :=
    parseAbsorb_absorbA p s0 (p.lbl 0) (p.enc m0) (p.encLen m0)
  exact ⟨OracleDecisionMultiDecoderLift.public_walk_one p _ 26 _ _ _ _ _ _ pub zero
      look2 look1 ha hroot,
    OracleDecisionMultiDecoderLift.fixed_walk_one p _ 26 _ _ _ _ _ _ _ zero
      look2 look1 ha hfroot⟩

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

#print axioms support_fibers
#print axioms support_walks
#print axioms support_recognized
end AspisR1.OraclePortRowAwareWitnessD2
end
