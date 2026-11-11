import RPz7_ExtractedDigest32Transcript
import PIN2_NHG_PublicCarrier

/-! PIN2 W6 (2026-11-11): PIN2 counterparts of `JFv_TranscriptInitial.success`'s
step, `JFu_TranscriptSeed.source/public_source` and `JFu_TranscriptLength.converted`,
stated on Stream C's PIN2 emission of `r1_semantic::public_transcript` and
`r1_wire::SemanticTranscript::new` (`PIN2_NEWGATE_r1_semantic`).  The digest input
is written with the release `TranscriptStep.initParts` (the PIN2 `DOMAIN` literal is
the release literal, `domain_eq`), so the seed equation of the fixture keeps its
form; only the length word changes (1455 -> 1520).  `pin2Digest` carries a release
Digest32 dictionary to the PIN2 dictionary type field for field (same `digest`
function, same `Copy` instance).  New module; no release counterpart. -/
set_option autoImplicit false
namespace AspisR1.PIN2W6_TranscriptSeed
open Aeneas Aeneas.Std Result

abbrev D32 := AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32
abbrev Transcript := AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript
abbrev NewPublic := AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public

def pin2Digest {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) : D32 H :=
  { coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest }

/-- The PIN2 emission's `DOMAIN` is the release literal. -/
theorem domain_eq : AspisR1PublicPreparationPIN2.r1_wire.DOMAIN = AspisR1PublicPreparation.r1_wire.DOMAIN := by
  unfold AspisR1PublicPreparationPIN2.r1_wire.DOMAIN AspisR1PublicPreparation.r1_wire.DOMAIN
  rfl

theorem new_of_length {H : Type} (D : D32 H) (hash : H)
    (bytes : Slice U8) (root : Array U8 32#usize) (length : U32)
    (hlen : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
      (Slice.len bytes) = ok (.Ok length)) :
    AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new D hash bytes root =
      (do let state ← D.digest hash (AspisR1PublicPreparation.TranscriptStep.initParts bytes root length)
          ok (.Ok ({ state, hash, next_row := 0#u8 } : Transcript H))) := by
  simp only [AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new, hlen,
    PCWN_NewLib.core.result.Result.map_err, PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
    lift, bind_tc_ok, AspisR1PublicPreparation.TranscriptStep.initParts, domain_eq]

theorem source {H : Type} (D : D32 H) (hash : H)
    (bytes : Slice U8) (root : Array U8 32#usize) (length : U32)
    (converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
      (Slice.len bytes) = ok (.Ok length)) (state : Array U8 32#usize)
    (digest : D.digest hash (AspisR1PublicPreparation.TranscriptStep.initParts bytes root length) = ok state) :
    AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new D hash bytes root =
      ok (.Ok (⟨state, hash, 0#u8⟩ : Transcript H)) := by
  rw [new_of_length D hash bytes root length converted, digest, bind_tc_ok]

/-- Semantic serialization (PIN2 `public_bytes`) is the initializer's byte input. -/
theorem public_source {H : Type} (D : D32 H) (hash : H)
    (pub : NewPublic) (encoded : alloc.vec.Vec U8)
    (serialized : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes pub =
      ok (.Ok encoded))
    (root : Array U8 32#usize) (length : U32)
    (converted : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from
      (Slice.len (alloc.vec.Vec.deref encoded)) = ok (.Ok length))
    (state : Array U8 32#usize)
    (digest : D.digest hash (AspisR1PublicPreparation.TranscriptStep.initParts
      (alloc.vec.Vec.deref encoded) root length) = ok state) :
    AspisR1PublicPreparationPIN2.r1_semantic.public_transcript D pub hash root =
      ok (.Ok (⟨state, hash, 0#u8⟩ : Transcript H)) := by
  unfold AspisR1PublicPreparationPIN2.r1_semantic.public_transcript
  simp only [serialized, bind_tc_ok, PCWN_NewLib.core.result.Result.map_err,
    PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch]
  exact source D hash _ root length converted state digest

theorem converted (bytes : Slice U8) (size : bytes.length = 1520) :
    core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len bytes) = ok (.Ok 1520#u32) := by
  have spec : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len bytes)
      ⦃ out => out = .Ok 1520#u32 ⦄ := by
    have len : (Slice.len bytes).val = 1520 := by scalar_tac
    step*
    obtain ⟨x, same, value⟩ := out_post1 (by scalar_tac)
    rw [same]
    congr 1
    scalar_tac
  obtain ⟨out, call, same⟩ := WP.spec_imp_exists spec
  rw [same] at call
  exact call

#print axioms domain_eq
#print axioms new_of_length
#print axioms source
#print axioms public_source
#print axioms converted
end AspisR1.PIN2W6_TranscriptSeed
