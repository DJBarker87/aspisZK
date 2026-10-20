import OracleDecisionMultiDecoderFacts
import OracleDecisionMultiDecoderLift

/-! A concrete decoder counterexample: a literal binary-node preimage can be
an ordinary row-one absorb address. The table is finite (three earlier
transcript cells, plus one leaf cell). No huge address universe is evaluated.
This refutes first-byte separation as a zero-start argument. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OracleDecisionMultiDecoder
open FS FS2 FS2.Duplex R0C.V3 AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw
open CanonicalAddressEmbedding
open OracleDecisionMultiTree

def m0 : SelectedTranscriptParams.Message := ⟨PublicInitFrame.emptyRecord, by decide⟩
def m1 : SelectedTranscriptParams.Message := ⟨List.replicate 31 0, by decide⟩
def records : List (Rec SelectedTranscriptParams.Message) := [(s0, absorbed, m0, endpoint)]

attribute [local irreducible] table RawBoundedTrace.table InitialWalk.walk
  InitialPublicWalk.walk

theorem walks :
    InitialPublicWalk.walk p (RawBoundedTrace.table L table) 27 endpoint =
      some ((pub,zero), RawRoundDecode.encode p 0 records) ∧
    InitialWalk.walk p pub.pubBytes (RawBoundedTrace.table L table) 27 endpoint =
      some (zero, RawRoundDecode.encode p 0 records) := by
  have hp : PublicInitParse.parse pub.pubBytes initial = some zero :=
    PublicInitParse.parse_addr [] (by decide) (by decide) zero
  have hr := RawPublicInitParser.of_fixed_parse pub initial zero rfl hp
  have ha : parseAbsorb row0 = some (s0, p.lbl 0, p.enc m0) :=
    parseAbsorb_absorbA p s0 (p.lbl 0) (p.enc m0) (p.encLen m0)
  have hroot : InitialPublicWalk.rootAt (RawBoundedTrace.table L table) s0 = some (pub,zero) := by
    rw [InitialPublicWalk.rootAt, lookups.1, Option.bind_some, hr]
  have hfroot : InitialWalk.rootAt pub.pubBytes (RawBoundedTrace.table L table) s0 = some zero := by
    rw [InitialWalk.rootAt, lookups.1]
    exact hp
  exact ⟨OracleDecisionMultiDecoderLift.public_walk_one p _ 26 s0 absorbed endpoint _ _ row0 pub zero
      lookups.2.2 lookups.2.1 ha hroot,
    OracleDecisionMultiDecoderLift.fixed_walk_one p _ 26 s0 absorbed endpoint _ _ _ row0 zero
      lookups.2.2 lookups.2.1 ha hfroot⟩


#print axioms walks
end AspisR1.OracleDecisionMultiDecoder
end
