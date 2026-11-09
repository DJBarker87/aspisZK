import NNH_S1HostCodec
import NNV_FinishTerminal
import LIB_VDomains
import LIB_S1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOM_TerminalDomain
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

/-- The literal installed op21 (NNH_S1HostCodec.validate) returns Ok exactly when
the frozen native validator (CLOSED276) returns Ok at the SAME statement carrier. -/
theorem validate_native (st : NNH_S1HostCodec.Statement)
 (good : NNH_S1HostCodec.validate st = .ok (.Ok ())) :
 NMT_345.validateCall (NNH_S1DecodeOk.carrier st) = .ok (.Ok ()) := by
 unfold NNH_S1HostCodec.validate at good
 cases h : NMT_345.validateCall (NNH_S1DecodeOk.carrier st) with
 | ok r =>
  cases r with
  | Ok u => cases u; rfl
  | Err e => simp only [h] at good <;> cases good
 | fail e => simp only [h] at good <;> cases good
 | div => simp only [h] at good <;> cases good

theorem validate_iff (st : NNH_S1HostCodec.Statement) :
 NNH_S1HostCodec.validate st = .ok (.Ok ()) ↔
 NMT_345.validateCall (NNH_S1DecodeOk.carrier st) = .ok (.Ok ()) :=
 ⟨validate_native st, fun h => NNH_S1HostCodec.validate_ok st ((LIBC_S1.valid_iff _).mpr h)⟩

/-- Digest half of the terminal domain on the reached 345 path: the installed
validator's Ok at the decoded statement gives publicDigestDom of the SAME
library semantic public that 345 passes to 328 (C.semanticPublic). -/
theorem validated_digest (st : NNH_S1HostCodec.Statement)
 (good : NNH_S1HostCodec.validate st = .ok (.Ok ())) :
 LIB_VPublicDomain.publicDigestDom (NNH_Libraries.C.semanticPublic (NNH_S1DecodeOk.carrier st)) :=
 LIB_S1.validated_public _ ((LIBC_S1.valid_iff _).mpr (validate_native st good))

/-- The same at the library statement (library validator true). -/
theorem library_digest (st : NNH_Libraries.C.Statement)
 (good : NNH_Libraries.C.validateStatement st = true) :
 LIB_VPublicDomain.publicDigestDom (NNH_Libraries.C.semanticPublic st) :=
 LIB_S1.validated_public st good

/-- Asset half: the returned public transcript (LIB_VDomains.eval_asset). -/
theorem asset (pub : Public) (r : RSL.B32) (env : RSL.Env) (t : Transcript)
 (returned : LIB_VLib.publicTranscriptValue (pub,r) env = .ok t) :
 LIB_VPublicDomain.publicAssetDom pub :=
 LIB_VDomains.eval_asset (pub,r) env t returned

/-- Full terminal Domain at the SAME public from the two halves. -/
theorem domain (a : LIB_VTerminal.Args) (r : RSL.B32) (env : RSL.Env) (t : Transcript)
 (digest : LIB_VPublicDomain.publicDigestDom a.1)
 (returned : LIB_VLib.publicTranscriptValue (a.1,r) env = .ok t) :
 LIB_VTerminal.Domain a :=
 ⟨digest, asset a.1 r env t returned⟩

/-- Reached form: the terminal's public is the semantic public of a statement
the installed op21 accepted, and the public transcript returned. -/
theorem reached (st : NNH_S1HostCodec.Statement)
 (good : NNH_S1HostCodec.validate st = .ok (.Ok ()))
 (a : LIB_VTerminal.Args) (same : a.1 = NNH_Libraries.C.semanticPublic (NNH_S1DecodeOk.carrier st))
 (r : RSL.B32) (env : RSL.Env) (t : Transcript)
 (returned : LIB_VLib.publicTranscriptValue (a.1,r) env = .ok t) :
 LIB_VTerminal.Domain a := by
 refine domain a r env t ?_ returned
 rw [same]
 exact validated_digest st good

/-- Converse terminal port on the Domain: a native Ok terminal is the SAME library value. -/
theorem terminal (a : LIB_VTerminal.Args) (env : RSL.Env) (dom : LIB_VTerminal.Domain a)
 (raw : LIB_VScalarCarriers.RawQ)
 (h : FIq_Terminal.terminal a.1 (claimsRaw a.2.1) (alphaRaw a.2.2.1) (challengesRaw a.2.2.2) = .ok (.Ok raw)) :
 ∃ q, LIB_VLib.terminalQm31Value a env = .ok q ∧ LIB_VScalarCarriers.toRaw q = raw := by
 obtain ⟨n, run, image⟩ := FIq_Terminal.reached _ _ _ _ raw h
 have hn : LIB_VTerminal.native a = .ok (.Ok n) := run
 have ex := LIB_VTerminal.model_exact a dom
 rw [hn, bind_tc_ok] at ex
 obtain ⟨out, hm, img⟩ := NNV_ResultOkPort.mapped _ _ _ ex
 cases out with
 | error e => cases img
 | ok q =>
  refine ⟨q, ?_, ?_⟩
  · change LIB_VResult.value id (.error ()) (LIB_VTerminal.model a) = _
    rw [hm]
    rfl
  · have e : LIB_VTerminalCarriers.scalar q = n := Except.ok.inj img
    subst e
    subst image
    rfl

#print axioms validate_native
#print axioms validate_iff
#print axioms validated_digest
#print axioms library_digest
#print axioms asset
#print axioms domain
#print axioms reached
#print axioms terminal
end AspisR1.NOM_TerminalDomain
end
