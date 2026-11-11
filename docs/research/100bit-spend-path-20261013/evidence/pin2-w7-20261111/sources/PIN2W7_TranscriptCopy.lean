import ExtractedPublicPreparationBinding
/-! PIN2 W7 (2026-11-11).  Field copies between the frozen preparation
extraction's transcript carriers (`AspisR1PublicPreparation.aspis_core.Digest32`,
`r1_wire.SemanticTranscript`) and the PIN2 emission's (`PIN2_NEWGATE_r1_semantic`),
and the fact that `SemanticTranscript.new` agrees across the two emissions on
the same bytes.  Only `public_bytes` changed at PIN2; `SemanticTranscript.new`
and `r1_wire.DOMAIN` are the same Rust items (same 38 domain bytes, proved by
`domain_eq`).  This lets consumers keep the frozen transcript types (which the
rest of the semantic trace uses) while the public-input bytes are the PIN2
ones. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.PIN2W7_TranscriptCopy

def digest {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) :
    AspisR1PublicPreparationPIN2.aspis_core.digest.Digest32 H :=
  { coremarkerCopyInst := D.coremarkerCopyInst, digest := D.digest }

def transcript {H : Type} (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) :
    AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript H :=
  { state := t.state, hash := t.hash, next_row := t.next_row }

/-- The two emissions' `r1_wire.DOMAIN` are the same 38 bytes. -/
theorem domain_eq :
    AspisR1PublicPreparationPIN2.r1_wire.DOMAIN = AspisR1PublicPreparation.r1_wire.DOMAIN := by
  unfold AspisR1PublicPreparationPIN2.r1_wire.DOMAIN AspisR1PublicPreparation.r1_wire.DOMAIN
  rfl

theorem new_eq {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H) (hash : H)
    (bytes : Slice U8) (root : Array U8 32#usize)
    (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (h : AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new (digest D) hash bytes root =
      ok (.Ok (transcript t))) :
    AspisR1PublicPreparation.r1_wire.SemanticTranscript.new D hash bytes root = ok (.Ok t) := by
  unfold AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new at h
  unfold AspisR1PublicPreparation.r1_wire.SemanticTranscript.new
  cases r : core.convert.num.ptr_try_from_impls.TryFromU32Usize.try_from (Slice.len bytes) with
  | fail e => simp only [r, bind_tc_fail] at h; cases h
  | div => simp only [r, bind_tc_div] at h; cases h
  | ok v =>
    cases v with
    | Err e =>
      simp only [r, bind_tc_ok, PCWN_NewLib.core.result.Result.map_err,
        AspisR1PublicPreparationPIN2.r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError.call_once,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from] at h
      cases h
    | Ok n =>
      simp only [r, bind_tc_ok, PCWN_NewLib.core.result.Result.map_err,
        PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch, lift] at h
      simp only [r, bind_tc_ok, core.result.Result.map_err,
        core.result.Result.Insts.CoreOpsTry.branch, lift]
      simp only [digest] at h
      generalize hd : D.digest hash _ = digested at h
      generalize hd2 : D.digest hash _ = digested2
      have same : digested2 = digested := by rw [← hd, ← hd2, domain_eq]
      subst same
      cases digested2 with
      | fail e => simp only [bind_tc_fail] at h; cases h
      | div => simp only [bind_tc_div] at h; cases h
      | ok st =>
        simp only [bind_tc_ok] at h ⊢
        cases t
        simp only [transcript] at h
        cases h
        rfl
/-- PIN2 `public_transcript` success, read back on the frozen transcript type:
the PIN2 serializer succeeds and the frozen `SemanticTranscript.new` on those
bytes returns the same transcript. -/
theorem public_transcript_split {H : Type} (D : AspisR1PublicPreparation.aspis_core.Digest32 H)
    (q : AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H)
    (root : Array U8 32#usize) (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H)
    (h : AspisR1PublicPreparationPIN2.r1_semantic.public_transcript (digest D) q hash root =
      ok (.Ok (transcript t))) :
    ∃ bytes : alloc.vec.Vec U8,
      AspisR1PublicPreparationPIN2.pool_v1.pair_forest_semantic_terminal.r0.Public.public_bytes q =
        ok (.Ok bytes) ∧
      AspisR1PublicPreparation.r1_wire.SemanticTranscript.new D hash (alloc.vec.Vec.deref bytes) root =
        ok (.Ok t) := by
  obtain ⟨bytes, hs, _, ht⟩ := AspisR1.PIN2_NHG_PublicCarrier.same_execution (digest D) q hash root (transcript t) h
  exact ⟨bytes, hs, new_eq D hash _ root t ht⟩

#print axioms domain_eq
#print axioms new_eq
#print axioms public_transcript_split
end AspisR1PublicPreparation.PIN2W7_TranscriptCopy
