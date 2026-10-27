import RPz7_PreparedSourcePowersEntryV1
import UnrolledWideParserRefinement
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PreparedParsedInactiveV1
open AspisR1ClaimPreparedBridge
open AspisR1CurrentPreparedClaim.Concrete
abbrev ParserWide := AspisR1CandidateParser.field.wide_exact.WideExact

def fromParser (x : ParserWide) : PE :=
  { c0 := { c0 := {a:=x.c0.c0.a,b:=x.c0.c0.b},c1:={a:=x.c0.c1.a,b:=x.c0.c1.b} },
    c1 := { c0 := {a:=x.c1.c0.a,b:=x.c1.c0.b},c1:={a:=x.c1.c1.a,b:=x.c1.c1.b} } }

/-- Retained unrolled decoder with an explicit field-preserving carrier map.
The actual View caller installation is a separate source obligation. -/
def parseInactive (bytes : Slice U8) : Result (Option PE) := do
  let value ← AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled bytes
  ok (value.map fromParser)

theorem parsed_canonical (bytes : Slice U8) (value : PE)
    (h : parseInactive bytes=ok (some value)) :
    bytes.val.length=32 ∧ Canonical (toClaimE value) := by
  unfold parseInactive at h
  cases hp : AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes_unrolled bytes with
  | fail e => simp only [hp,bind_tc_fail] at h; cases h
  | div => simp only [hp,bind_tc_div] at h; cases h
  | ok parsed =>
    simp only [hp,bind_tc_ok] at h
    cases parsed with
    | none => cases h
    | some x =>
      have hv : fromParser x=value := Option.some.inj (Result.ok.inj h)
      obtain ⟨hlen,hcanonical⟩ := AspisR1.UnrolledWideParserRefinement.slice_success_canonical bytes x hp
      refine ⟨hlen,?_⟩
      rw [← hv]
      change (((x.c0.c0.a.val < 2147483647 ∧ x.c0.c0.b.val < 2147483647) ∧
        (x.c0.c1.a.val < 2147483647 ∧ x.c0.c1.b.val < 2147483647)) ∧
        ((x.c1.c0.a.val < 2147483647 ∧ x.c1.c0.b.val < 2147483647) ∧
        (x.c1.c1.a.val < 2147483647 ∧ x.c1.c1.b.val < 2147483647)))
      exact hcanonical

open FS FS2 FS2.Duplex AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge AspisR1PublicPreparation.SourceDigestOracle
open AspisR1ClaimPreparedBridge.InstalledMeaning
open AspisR1PublicPreparation
open AspisR1PreparedSourcePowersBoundariesV1 AspisR1PreparedSourcePowersJointRankV1

theorem entry_parsed_inactive_original_payload_and_rank {H M Cv : Type} {L : Nat}
    (sampling : PreparedModel.Boundaries)
    (embed : aspis_core.field.M31 → Result aspis_core.field.WideExact)
    (D : aspis_core.Digest32 H) (p : FS2.Duplex.Params M Cv L)
    (pubInput : Slice U8) (root : TranscriptStep.Bytes32) (length : U32)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H)
    (out : verifier.Prepared)
    (scratch scratchIn : Array AspisR1ClaimPreparedBridge.PE 29#usize)
    (inactiveBytes : Slice U8)
    (hparse : parseInactive inactiveBytes=ok (some v.inactive))
    (h : PreparedScratchModel.entry (sourceBoundaries (installedBoundaries sampling embed))
      D sem v hash scratchIn=ok (.Ok out,scratch)) :
    inactiveBytes.val.length=32 ∧
    (Canonical (toClaimE out.gamma) ∧ Canonical (toClaimE out.kappa)) ∧
    OriginalPayloadClaimMeaning sem v.y1 (toClaimE v.inactive)
      (toClaimE out.gamma) (toClaimE out.kappa) (toClaimE out.claim) (mapArray toClaimE scratch) ∧
    JointRankTrace sampling embed D p pubInput root length sem v hash out scratch := by
  obtain ⟨hlen,hcanonical⟩ := parsed_canonical inactiveBytes v.inactive hparse
  exact ⟨hlen,AspisR1PreparedSourcePowersEntryV1.entry_sourcePowers_original_payload_and_rank
    sampling embed D p pubInput root length sem v hash out scratch scratchIn hcanonical h⟩

#print axioms parsed_canonical
#print axioms entry_parsed_inactive_original_payload_and_rank
end AspisR1PreparedParsedInactiveV1
