import NBR_SemanticFinish
set_option autoImplicit false
namespace AspisR1.NCA_ObservedControl
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem parse_error (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (hash : H) (obs : Option (verifier.Phase → Result Unit)) (error : r1_wire.Error)
    (call : PrefixAdapter.parseAccepted bytes=ok (.Err error)) :
    VerifyPrefix.verify F D pub bytes hash obs=ok (.Err error) := by
  simp only [VerifyPrefix.verify,call,bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

theorem public_error (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (hash : H) (obs : Option (verifier.Phase → Result Unit)) (pre : r1_wire.Prefix)
    (error : r1_wire.Error) (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (call : r1_semantic.public_transcript D pub hash pre.c1_root=ok (.Err error)) :
    VerifyPrefix.verify F D pub bytes hash obs=ok (.Err error) := by
  simp only [VerifyPrefix.verify,parsed,call,VerifyPrefix.mark,bind_tc_ok,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

theorem begin_error (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (hash : H) (obs : Option (verifier.Phase → Result Unit)) (pre : r1_wire.Prefix)
    (initial after : r1_wire.SemanticTranscript H) (error : r1_wire.Error)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (started : r1_semantic.public_transcript D pub hash pre.c1_root=ok (.Ok initial))
    (call : r1_wire.begin D pre initial=ok (.Err error,after)) :
    VerifyPrefix.verify F D pub bytes hash obs=ok (.Err error) := by
  simp only [VerifyPrefix.verify,parsed,started,call,VerifyPrefix.mark,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from]

/-- Entire finish Result, including error/fail/div, is returned verbatim.
This is a control law; chronological digest-prefix association is separate. -/
theorem finish_result (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8)
    (hash : H) (obs : Option (verifier.Phase → Result Unit)) (pre : r1_wire.Prefix)
    (initial after : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges)
    (parsed : PrefixAdapter.parseAccepted bytes=ok (.Ok pre))
    (started : r1_semantic.public_transcript D pub hash pre.c1_root=ok (.Ok initial))
    (call : r1_wire.begin D pre initial=ok (.Ok challenges,after)) :
    VerifyPrefix.verify F D pub bytes hash obs=F D pub pre after challenges obs := by
  simp only [VerifyPrefix.verify,parsed,started,call,VerifyPrefix.mark,bind_tc_ok,Aeneas.Std.uncurry,
    core.result.Result.Insts.CoreOpsTry.branch]

#print axioms parse_error
#print axioms public_error
#print axioms begin_error
#print axioms finish_result
end AspisR1.NCA_ObservedControl
