import S9CurrentCheckpointKDecoderCMMapV1
import AspisR1DecodeKFullParserCanonicalityCMQ

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9CurrentCheckpointKDecoderAcceptedV1
open AspisR1S9CurrentCheckpointKDecoderCMMapV1
abbrev CurQM := AspisR1S9CurrentCheckpointKDecoderV1.field.QM31
abbrev OldQM := AspisR1DecodeKFullV10.aspis_core.field.QM31
def toOldQM (q : CurQM) : OldQM := ⟨toOldCM q.c0,toOldCM q.c1⟩
private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (out : B)
    (h : (do let x ← m; k x) = ok out) : ∃ x, m = ok x ∧ k x = ok out := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Accepted-run source transport only: no all-outcomes equality is claimed. -/
theorem qm_success_to_old (bytes : Slice U8) (q : CurQM)
    (success : AspisR1S9CurrentCheckpointKDecoderV1.field.QM31.from_le_bytes bytes = .ok (some q)) :
    AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes bytes = .ok (some (toOldQM q)) := by
  unfold AspisR1S9CurrentCheckpointKDecoderV1.field.QM31.from_le_bytes at success
  obtain ⟨s0,hs0,h0⟩ := bind_success _ _ _ success
  obtain ⟨o0,ho0,hbranch0⟩ := bind_success _ _ _ h0
  have hdisc : Aeneas.Std.read_discriminant
      (none : Option Aeneas.Std.core.convert.Infallible) = 0#isize := rfl
  cases o0 with
  | none =>
    simp [AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
      Aeneas.Std.massert,hdisc] at hbranch0
  | some a =>
    simp only [AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      bind_tc_ok] at hbranch0
    obtain ⟨s1,hs1,h1⟩ := bind_success _ _ _ hbranch0
    obtain ⟨o1,ho1,hbranch1⟩ := bind_success _ _ _ h1
    cases o1 with
    | none =>
      simp [AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual,
        Aeneas.Std.massert,hdisc] at hbranch1
    | some b =>
      simp only [AspisR1S9CurrentCheckpointKDecoderV1.core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        bind_tc_ok] at hbranch1
      have hq : ({c0 := a,c1 := b} : CurQM) = q := Option.some.inj (Result.ok.inj hbranch1)
      subst q
      have hold0 := cm_decoder_map s0
      rw [ho0] at hold0
      have old0 : AspisR1DecodeKFullV10.aspis_core.field.CM31.from_le_bytes s0 = .ok (some (toOldCM a)) := hold0.symm
      have hold1 := cm_decoder_map s1
      rw [ho1] at hold1
      have old1 : AspisR1DecodeKFullV10.aspis_core.field.CM31.from_le_bytes s1 = .ok (some (toOldCM b)) := hold1.symm
      unfold AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes
      simp only [hs0,bind_tc_ok,old0,hs1,old1,
        AspisR1DecodeKFullV10.core.option.Option.Insts.CoreOpsTry_traitTry.branch,toOldQM]

def Canonical (q : CurQM) : Prop :=
  q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
  q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

theorem current_decoder_success_canonical (bytes : Slice U8) (q : CurQM)
    (success : AspisR1S9CurrentCheckpointKDecoderV1.field.QM31.from_le_bytes bytes = .ok (some q)) :
    Canonical q := by
  have hold := qm_success_to_old bytes q success
  have hc := AspisR1DecodeKFullParserCanonicality.qm31_from_le_bytes_success_canonical bytes (toOldQM q) hold
  have hp : AspisR1DecodeKFullV10.aspis_core.field.P.val = 2147483647 := by
    unfold AspisR1DecodeKFullV10.aspis_core.field.P
    rfl
  simpa only [Canonical,toOldQM,toOldCM,hp] using hc

#print axioms qm_success_to_old
#print axioms current_decoder_success_canonical
end AspisR1S9CurrentCheckpointKDecoderAcceptedV1
