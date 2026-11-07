import LIB_VParse
import LIB_VPublicAsset
import LIB_VTerminal
set_option autoImplicit false
noncomputable section
namespace LIB_VDomains
open Aeneas Aeneas.Std LIB_VCarriers
open AspisR1PublicPreparation
/-- Exactly the map's hd clause; asset is derived inside137 from CLOSED131. -/
abbrev publicDom := LIB_VPublicDomain.publicDigestDom
/-- The noncanonical-asset branch is rejected by public_bytes before136.
The remaining clauses are the original source-borrow envelope. Canonical field
clauses are discharged by the selected input carriers and child exports. -/
def finishInputDom (pub : Public) (p : Prefix) (_ : Transcript) (_ : Challenges) : Prop :=
 publicDom pub ∧ LIB_VPublicDomain.publicAssetDom pub ∧ p.source.val.length≤57607
theorem eval_source (b : RSL.Bytes) (p : Prefix) (h : LIB_VParsePrefix.eval b=.ok p) :
 LIB_Carriers.bytes p.source=b := by
 classical
 unfold LIB_VParsePrefix.eval LIB_VParsePrefix.model at h
 split at h
 · rename_i bounded
   unfold LIB_VParsePrefix.parseRaw at h
   split at h
   · have same := Except.ok.inj h
     subst p
     exact LIB_Bytes.bytes_from b bounded
   · cases h
   · cases h
   · cases h
 · cases h
theorem eval_prefix_bound (b : RSL.Bytes) (h : LIB_VParsePrefix.semanticBytesDom b)
 (p : Prefix) (returned : LIB_VParsePrefix.eval b=.ok p) : p.source.val.length≤57607 := by
 have len := congrArg List.length (eval_source b p returned)
 rw [NMS_R2N_RSLScalars.bytes_length] at len
 rw [len]
 exact h
theorem eval_asset (a : Public × RSL.B32) (env : RSL.Env) (t : Transcript)
 (returned : LIB_VPublicTranscript.eval a env=.ok t) : LIB_VPublicDomain.publicAssetDom a.1 := by
 unfold LIB_VPublicTranscript.eval at returned
 cases result : (PreparedHashCode.run (LIB_VPublicTranscript.code a env)).2 with
 | fail e => simp only [result,LIB_VResult.value] at returned;cases returned
 | div => simp only [result,LIB_VResult.value] at returned;cases returned
 | ok reply =>
  cases reply with
  | Err e => simp only [result,LIB_VResult.value,LIB_VRecords.host] at returned;cases returned
  | Ok native => exact LIB_VPublicAsset.code_asset a env native result
/-- The SAME staged evaluators establish finishInputDom. No child result,
success, arbitrary Ops dictionary, or caller-provided finish-domain premise. -/
theorem finish_of_eval (pub : Public) (b : RSL.Bytes) (env : RSL.Env)
 (hp : publicDom pub) (hb : LIB_VParsePrefix.semanticBytesDom b) :
 match LIB_VParsePrefix.eval b with
 | .error _=>True
 | .ok p=>match LIB_VPublicTranscript.eval (pub,c1Root p) env with
   | .error _=>True
   | .ok initial=>match LIB_VBegin.eval (p,initial) env with
     | .error _=>True
     | .ok (c,t)=>finishInputDom pub p t c := by
 cases parsed : LIB_VParsePrefix.eval b with
 | error e => trivial
 | ok p =>
  cases transcript : LIB_VPublicTranscript.eval (pub,c1Root p) env with
  | error e => trivial
  | ok initial =>
   cases begun : LIB_VBegin.eval (p,initial) env with
   | error e => trivial
   | ok pair => exact ⟨hp,eval_asset _ env initial transcript,eval_prefix_bound b hb p parsed⟩
#print axioms eval_source
#print axioms eval_prefix_bound
#print axioms eval_asset
#print axioms finish_of_eval
end LIB_VDomains
