import NJG_CarrierBack
import NJG_FinishInstall
import NJG_ObservedStages
set_option autoImplicit false
namespace AspisR1.NJG_ObservedInstall
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NJG_Carriers NJG_InputCarriers NJG_Results

/-- Complete outer/inner Result transport, preserving every error payload. -/
def lower {T U : Type} (convert : T→U) : Result (core.result.Result T ME) → Result (core.result.Result U EE)
 | .ok (.Ok value)=>.ok (.Ok (convert value))
 | .ok (.Err error)=>.ok (.Err (downError error))
 | .fail error=>.fail error
 | .div=>.div

def lowerBegin {H : Type} :
 Result (core.result.Result r1_wire.Challenges ME × r1_wire.SemanticTranscript H) →
 Result (core.result.Result NIX_EmittedTypes.aspis_core.state_only_prefix.r0.Challenges EE × NIX_EmittedTypes.r1_wire.SemanticTranscript H)
 | .ok (reply,post)=>.ok ((match reply with | .Ok q=>.Ok (downChallenge q) | .Err error=>.Err (downError error)),downTranscript post)
 | .fail error=>.fail error
 | .div=>.div

/-- Fix all four native-root dictionary fields to actual source child functions;
finish uses the fresh E001 body. This is no child-law/endpoint hypothesis. The
native packets for these fields still require composed admission. -/
def install {H : Type} (R : RoundModel.Boundaries) (F : FinishModel.Boundaries) :
 NIX_ObservedBody.Boundaries H where
 parse:=fun bytes=>lower downPrefix (PrefixAdapter.parseAccepted bytes)
 publicTranscript:=fun D pubdata hash root=>lower downTranscript
  (r1_semantic.public_transcript (upDigest D) (upPublic pubdata) hash root)
 begin:=fun D pre t=>lowerBegin (r1_wire.begin (upDigest D) (upPrefix pre) (upTranscript t))
 finish:=fun D pubdata pre t c _obs=>downResult
  (NJG_FinishBody.r1_semantic.verify_finish (NJG_FinishInstall.install R F)
   (upDigest D) (upPublic pubdata) (upPrefix pre) (upTranscript t) (upChallenge c) none)

/-- Complete SAME-value raw-root -> adopted-root equation: all nine Verified
fields, all WireError fields, ambient failure/divergence. No endpoint or
successful-child premise. This is SOURCE/model support, not native op9 closure. -/
theorem source {H : Type} (R : RoundModel.Boundaries) (F : FinishModel.Boundaries)
 (D : NIX_EmittedTypes.aspis_core.digest.Digest32 H)
 (pubdata : NIX_EmittedTypes.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (bytes : Slice U8) (hash : H) :
 upResult (NIX_ObservedBody.emitted (install R F) D pubdata bytes hash none)=
 VerifyPrefix.verify (FinishModel.finish R (NJG_FinishInstall.model F))
  (upDigest D) (upPublic pubdata) bytes hash none := by
 unfold NIX_ObservedBody.emitted VerifyPrefix.verify
 simp only [install,NIX_ObservedBody.mark,VerifyPrefix.mark,bind_tc_ok]
 cases hp:PrefixAdapter.parseAccepted bytes with
 | fail error=>rfl
 | div=>rfl
 | ok parsed=>cases parsed with
   | Err error=>simp only [lower,upResult,NJG_Results.error_back,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
   | Ok pre=>
     simp only [lower,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,NJG_CarrierBack.prefix_back]
     cases ht:r1_semantic.public_transcript (upDigest D) (upPublic pubdata) hash pre.c1_root with
     | fail error=>rfl
     | div=>rfl
     | ok reply=>cases reply with
       | Err error=>simp only [lower,upResult,NJG_Results.error_back,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
       | Ok t=>
         simp only [lower,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,NJG_CarrierBack.transcript]
         cases hb:r1_wire.begin (upDigest D) pre t with
         | fail error=>rfl
         | div=>rfl
         | ok pair=>rcases pair with ⟨reply,post⟩;cases reply with
           | Err error=>simp only [lowerBegin,upResult,NJG_Results.error_back,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch]
           | Ok c=>
             simp only [lowerBegin,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
              NJG_CarrierBack.transcript,NJG_CarrierBack.challenge,NJG_CarrierBack.result,
              NJG_FinishInstall.source]

#print axioms source
end AspisR1.NJG_ObservedInstall
