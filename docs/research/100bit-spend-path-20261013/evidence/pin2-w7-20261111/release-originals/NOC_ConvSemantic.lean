import NOC_FinishSource
import NNV_SemanticPrefix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_ConvSemantic
open Aeneas Aeneas.Std Result AspisR1PublicPreparation LIB_VCarriers

/-- Converse, public transcript: an Ok native transcript is the SAME library value. -/
theorem transcript (a : Public × RSL.B32) (env : RSL.Env) (t : Transcript)
 (h : r1_semantic.public_transcript (LIB_VCode.digest env) a.1 () (LIB_Env.nativeKey a.2) = .ok (.Ok t)) :
 LIB_VLib.publicTranscriptValue a env = .ok t := by
 change LIB_VResult.value LIB_VRecords.host (.error .Public)
  (PreparedHashCode.run (LIB_VPublicTranscript.code a env)).2 = .ok t
 rw [NNV_SemanticTranscript.source,h]
 rfl

/-- Converse, prefix parse. -/
theorem parse (source : Slice U8) (env : RSL.Env) (pre : r1_wire.Prefix)
 (h : PrefixAdapter.parseAccepted source = .ok (.Ok pre)) :
 ∃ p, LIB_VLib.parsePrefixValue (LIB_Carriers.bytes source) env = .ok p ∧ prefixRaw p = pre := by
 have raw := LIB_VParsePrefix.raw_exact source
 rw [← NNV_SemanticParse.association,h] at raw
 cases hm : LIB_VParsePrefix.parseRaw source with
 | ok out =>
  rw [hm,bind_tc_ok] at raw
  cases out with
  | ok p =>
   refine ⟨p,?_,?_⟩
   · change LIB_VResult.value id (.error (.Length 0#u8)) (LIB_VParsePrefix.model (LIB_Carriers.bytes source)) = .ok p
     rw [LIB_VParsePrefix.model_same,hm]
     rfl
   · have e := Result.ok.inj raw
     injection e
  | error e => have e' := Result.ok.inj raw; cases e'
 | fail e => rw [hm] at raw; simp only [bind_tc_fail] at raw; cases raw
 | div => rw [hm] at raw; simp only [bind_tc_div] at raw; cases raw

/-- Converse, begin. -/
theorem begin_ (a : Prefix × Transcript) (env : RSL.Env) (cs : r1_wire.Challenges) (after : Transcript)
 (h : r1_wire.begin (LIB_VCode.digest env) (prefixRaw a.1) a.2 = .ok (.Ok cs,after)) :
 ∃ c, LIB_VLib.beginValue a env = .ok (c,after) ∧ challengesRaw c = cs := by
 have ex := LIB_VBegin.model_exact a env
 rw [h,bind_tc_ok] at ex
 cases hm : LIB_VBegin.model a env with
 | ok out =>
  rw [hm,bind_tc_ok] at ex
  cases out with
  | ok pair =>
   rcases pair with ⟨c,t⟩
   have e := Except.ok.inj (Result.ok.inj ex)
   obtain ⟨e1,e2⟩ := Prod.mk.inj e
   subst e2
   refine ⟨c,?_,e1⟩
   change LIB_VResult.value id (.error .Terminal) (LIB_VBegin.model a env) = _
   rw [hm]
   rfl
  | error err => have e := Result.ok.inj ex; cases e
 | fail e => rw [hm] at ex; simp only [bind_tc_fail] at ex; cases ex
 | div => rw [hm] at ex; simp only [bind_tc_div] at ex; cases ex

/-- Converse, semantic rounds, at the native RoundModel call of the finish body. -/
theorem rounds (p : Prefix) (t : Transcript) (env : RSL.Env)
 (raw : aspis_core.field.QM31 × Array aspis_core.field.QM31 10#usize × Transcript)
 (h : RoundModel.rounds NJM_RoundJoin.R (LIB_VCode.digest env) (prefixRaw p) t = .ok (.Ok raw)) :
 ∃ r, LIB_VLib.semanticRoundsValue (p,t) env = .ok r ∧
 (LIB_VScalarCarriers.toRaw r.1,alphaRaw r.2.1,r.2.2) = raw := by
 have h' : (PreparedHashCode.run (LIB_VRounds.code (p,t) env)).2 = .ok (.Ok raw) :=
  (PreparedHashCode.run_value _).trans ((S1SemanticCode.rounds_erasure _ _ _ _).trans h)
 have ex := LIB_VRounds.model_exact (p,t) env
 rw [h',bind_tc_ok] at ex
 cases hm : LIB_VRounds.model (p,t) env with
 | ok out =>
  rw [hm,bind_tc_ok] at ex
  cases out with
  | ok r =>
   refine ⟨r,?_,?_⟩
   · change LIB_VResult.value id (.error .Terminal) (LIB_VRounds.model (p,t) env) = _
     rw [hm]
     rfl
   · exact Except.ok.inj (Result.ok.inj ex)
  | error err => have e := Result.ok.inj ex; cases e
 | fail e => rw [hm] at ex; simp only [bind_tc_fail] at ex; cases ex
 | div => rw [hm] at ex; simp only [bind_tc_div] at ex; cases ex

/-- Converse, circle sampling, at the native circle_validated call. -/
theorem circle (B : FinishModel.Boundaries) (t : Transcript) (r : Record) (env : RSL.Env)
 (z : Point) (after : Transcript)
 (h : FinishModel.circle_validated (F3M_CircleSource.install B) (LIB_VCode.digest env) t r = .ok (.Ok z,after)) :
 LIB_VLib.circleValue (t,r) env = .ok (z,after) := by
 have h' : (PreparedHashCode.run (NJM_CircleCode.source (LIB_VCode.digest env) t r)).2 = .ok (.Ok z,after) :=
  (congrArg Prod.snd (NJM_CircleCode.original B (LIB_VCode.digest env) t r)).symm.trans
   ((PreparedHashCode.run_value _).trans ((S1SemanticCode.circleValidated_erasure _ _ _ _).trans h))
 change LIB_VResult.value LIB_VCircle.project (.error .InvalidRow)
  (PreparedHashCode.run (LIB_VCircle.code (t,r) env)).2 = _
 change LIB_VResult.value LIB_VCircle.project (.error .InvalidRow)
  (PreparedHashCode.run (NJM_CircleCode.source (LIB_VCode.digest env) t r)).2 = _
 rw [h']
 rfl

/-- Converse, validated record. -/
theorem record (p : Prefix) (row : U8) (rec : Record)
 (h : r1_wire.Prefix.validated_record (prefixRaw p) row = .ok (.Ok rec)) :
 LIB_VRecordsAll.validatedRecord p row.val = .ok rec := by
 rw [LIB_VRecords.validated_exact] at h
 have e := Result.ok.inj h
 change LIB_VRecords.validatedRecord p row.val = _
 cases hv : LIB_VRecords.validatedRecord p row.val with
 | ok r => rw [hv] at e; injection e with e; rw [e]
 | error err => rw [hv] at e; cases e

/-- Converse, K29 decode on the derived record domain. -/
theorem decode (r : Record) (off : Usize) (domain : LIB_VDecode.Domain r off.val) (out' : Array LIB_VScalarCarriers.RawQ 29#usize)
 (h : AspisS1ExtractedRoundChildren.decodeMain 29#usize r off = .ok (.Ok out')) :
 ∃ out, LIB_VRecordsAll.decodeK29 r off.val = .ok out ∧ k29Raw out = out' := by
 rw [NNX_FinishDecodePort.source,LIB_VRecordsAll.decode_native r off domain.1 domain.2] at h
 have e := Result.ok.inj h
 cases hd : LIB_VRecordsAll.decodeK29 r off.val with
 | ok out => rw [hd] at e; injection e with e; exact ⟨out,rfl,e⟩
 | error err => rw [hd] at e; cases e

/-- Converse, row payload. -/
theorem payload (p : Prefix) (row : U8) (raw : Slice U8)
 (h : FinishModel.payload (prefixRaw p) row = .ok (.Ok raw)) :
 LIB_VRecordsAll.payload p row.val = .ok (LIB_Carriers.bytes raw) := by
 have m := LIB_VRecordsAll.payload_native p row
 rw [h,bind_tc_ok] at m
 exact (Result.ok.inj m).symm

/-- Ok-iff piece, claims: at a granted reservation the native claims call and
the library value are the SAME claims. -/
theorem claims (p : Prefix) (env : RSL.Env) (granted : env.reservation = true) :
 LIB_VLib.claimsValue p env = .ok (LIB_VClaims.value p) ∧
 ClaimsUnrolledFinish.claims (NP6_StdModel.calls (.Ok ())) (prefixRaw p) =
  .ok (.Ok (claimsRaw (LIB_VClaims.value p))) := by
 refine ⟨?_,LIB_VClaims.success_exact p⟩
 change (if env.reservation then .ok (LIB_VClaims.value p) else Except.error (r1_wire.Error.Allocation)) = _
 rw [granted]
 rfl
#print axioms transcript
#print axioms parse
#print axioms begin_
#print axioms rounds
#print axioms circle
#print axioms record
#print axioms decode
#print axioms payload
#print axioms claims
end AspisR1.NOC_ConvSemantic
end
