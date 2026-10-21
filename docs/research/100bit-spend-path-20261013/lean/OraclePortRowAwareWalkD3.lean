import OraclePortRowAwareWitnessD2

/-! Finite, fully cached row-zero history for the frozen node overlap.
Unlike the older witness, this table has no leaf answer equal to iv. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortRowAwareWalkD3
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalAddressEmbedding OracleDecisionMultiDecoder
open OraclePortRowAwareCausalD1

open OraclePortRowAwareWitnessD2
attribute [local irreducible] support RawBoundedTrace.table InitialWalk.walk InitialPublicWalk.walk

theorem support_walks :
    InitialPublicWalk.walk p (RawBoundedTrace.table L support) 27 endpoint =
      some ((pub,zero), RawRoundDecode.encode p 0 records) ∧
    InitialWalk.walk p pub.pubBytes (RawBoundedTrace.table L support) 27 endpoint =
      some (zero, RawRoundDecode.encode p 0 records) := by
  have c0 : CanonicalByteAddress.Canonical initial := by
    unfold initial PublicInitFrame.addr; apply CanonicalByteAddress.canonical_ofBytes
  have c1 : CanonicalByteAddress.Canonical row0 := by
    unfold row0 PublicInitFrame.row0 absorbA; apply CanonicalByteAddress.canonical_ofBytes
  have c2 : CanonicalByteAddress.Canonical advanced := by
    unfold advanced advanceA; apply CanonicalByteAddress.canonical_ofBytes
  have fibers := And.intro
    (bounded_fiber support initial c0 s0 support_fibers.1)
    (And.intro
      (bounded_fiber support row0 c1 absorbed support_fibers.2.1)
      (bounded_fiber support advanced c2 endpoint support_fibers.2.2))
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

#print axioms support_walks
end AspisR1.OraclePortRowAwareWalkD3
end
