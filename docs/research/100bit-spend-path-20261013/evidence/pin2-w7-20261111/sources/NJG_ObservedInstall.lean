import NJG_CarrierBack
import NJG_FinishInstall
import NJG_ObservedStages
import PIN2_S1SemanticCodeVerifyV1
import RPz7_S1SemanticCodeVerifyExactV1
/-! PIN2 W9 (2026-11-11), coordinator-approved DEFINITION CHANGE: the installed boundary child
`install.publicTranscript` is the lowered erase of the PIN2 public-transcript call on the
up-copies, `lower downTranscript (erase (S1SemanticCode.publicTranscriptPIN2 (upDigest D)
(upPublic pubdata) hash root))` (release: the frozen `r1_semantic.public_transcript`), because
that is the source child at PIN2.  parse, begin and finish children are unchanged.
STATEMENT CHANGE in `source`: its right-hand side is `prefixPIN2`, the frozen
`VerifyPrefix.verify` text with that one call replaced (frozen carriers throughout), in place of
`VerifyPrefix.verify`; the proof is the release case split with the same replacement.
New: `prefixPIN2`, `prefixPIN2_erasure` (`erase (verifyPIN2 (finish R B) ..) = prefixPIN2
(FinishModel.finish R B) ..`, the release `verify_erasure` script). -/
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

/-- The frozen `VerifyPrefix.verify` with its single public-transcript call replaced by the
erase of `S1SemanticCode.publicTranscriptPIN2` (the PIN2 call, read back on the frozen carriers). -/
def prefixPIN2 (F : VerifyPrefix.Finish)
  {H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (public1 : pool_v1.pair_forest_semantic_terminal.r0.Public)
  (bytes : Slice Std.U8) (hash : H)
  (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
  Result (core.result.Result (r1_semantic.Verified H) r1_wire.Error)
  := do
  let r ← PrefixAdapter.parseAccepted bytes
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue p =>
    VerifyPrefix.mark obs 0#u8
    let r1 ←
      PreparedHashCode.erase (S1SemanticCode.publicTranscriptPIN2 aspis_coreDigest32Inst public1 hash
        p.c1_root)
    let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
    match cf1 with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let (r2, val1) ← r1_wire.begin aspis_coreDigest32Inst p val
      let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
      match cf2 with
      | core.ops.control_flow.ControlFlow.Continue val2 =>
        VerifyPrefix.mark obs 1#u8
        F aspis_coreDigest32Inst public1 p val1 val2
          obs
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error)
          residual
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

private theorem bind_congr {A B : Type} (r : Result A) (f g : A → Result B)
    (h : ∀ a,f a=g a) : (r >>= f)=(r >>= g) :=
  congrArg (fun next => r >>= next) (funext h)

/-- The erased lifted PIN2 verifier is `prefixPIN2` (release `verify_erasure` script). -/
theorem prefixPIN2_erasure (R : RoundModel.Boundaries) (B : FinishModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
    (obs : Option (RPz7_PhaseIso.Phase → Result Unit)) :
    PreparedHashCode.erase (S1SemanticCode.verifyPIN2 (S1SemanticCode.finish R B) D pub bytes hash obs)=
      prefixPIN2 (FinishModel.finish R B) D pub bytes hash obs := by
  unfold S1SemanticCode.verifyPIN2 prefixPIN2
  repeat' first
    | (solve | exact PreparedHashCode.erase_lift _)
    | (solve | exact PreparedHashCode.erase_pure _)
    | (solve | apply S1SemanticCode.finish_erasure)
    | (solve | rfl)
    | (rw [PreparedHashCode.erase_bind]
       first | rw [PreparedHashCode.erase_lift] | rw [S1SemanticCode.begin_erasure]
       apply bind_congr
       intro x)
    | (rw [PreparedHashCode.erase_bind]
       apply bind_congr
       intro x)
    | (apply bind_congr;intro x)
    | split

/-- Fix all four native-root dictionary fields to actual source child functions;
finish uses the fresh E001 body. This is no child-law/endpoint hypothesis. The
native packets for these fields still require composed admission. -/
def install {H : Type} (R : RoundModel.Boundaries) (F : FinishModel.Boundaries) :
 NIX_ObservedBody.Boundaries H where
 parse:=fun bytes=>lower downPrefix (PrefixAdapter.parseAccepted bytes)
 publicTranscript:=fun D pubdata hash root=>lower downTranscript
  (PreparedHashCode.erase (S1SemanticCode.publicTranscriptPIN2 (upDigest D) (upPublic pubdata) hash root))
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
 prefixPIN2 (FinishModel.finish R (NJG_FinishInstall.model F))
  (upDigest D) (upPublic pubdata) bytes hash none := by
 unfold NIX_ObservedBody.emitted prefixPIN2
 simp only [install,NIX_ObservedBody.mark,VerifyPrefix.mark,bind_tc_ok]
 cases hp:PrefixAdapter.parseAccepted bytes with
 | fail error=>rfl
 | div=>rfl
 | ok parsed=>cases parsed with
   | Err error=>simp [lower,upResult,NJG_Results.error_back,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame,core.convert.FromSame.from]
   | Ok pre=>
     simp only [lower,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,NJG_CarrierBack.prefix_back]
     have root_eq:(downPrefix pre).c1_root=pre.c1_root:=rfl
     simp only [root_eq]
     cases ht:PreparedHashCode.erase (S1SemanticCode.publicTranscriptPIN2 (upDigest D) (upPublic pubdata) hash pre.c1_root) with
     | fail error=>rfl
     | div=>rfl
     | ok reply=>cases reply with
       | Err error=>simp [lower,upResult,NJG_Results.error_back,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame,core.convert.FromSame.from]
       | Ok t=>
         simp only [lower,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,NJG_CarrierBack.transcript]
         cases hb:r1_wire.begin (upDigest D) pre t with
         | fail error=>rfl
         | div=>rfl
         | ok pair=>rcases pair with ⟨reply,post⟩;cases reply with
           | Err error=>simp [lowerBegin,upResult,NJG_Results.error_back,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame,core.convert.FromSame.from]
           | Ok c=>
             dsimp only [lowerBegin]
             simp [lowerBegin,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
              NJG_CarrierBack.transcript,NJG_CarrierBack.challenge,NJG_CarrierBack.result,
              NJG_FinishInstall.source,core.convert.FromSame.from,NJG_Results.error_back]

 all_goals simp only [core.convert.FromSame.from]
 all_goals dsimp only
 all_goals simp only [NJG_CarrierBack.transcript,NJG_CarrierBack.challenge,NJG_CarrierBack.result,NJG_FinishInstall.source,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,core.convert.FromSame,core.convert.FromSame.from,NJG_Results.error_back,upResult]
 all_goals rfl

#print axioms prefixPIN2_erasure
#print axioms source
end AspisR1.NJG_ObservedInstall
