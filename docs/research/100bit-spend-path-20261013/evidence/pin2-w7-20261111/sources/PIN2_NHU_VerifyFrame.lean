import NHU_VerifyFrame
import PIN2_NEWGATE_verifyprefix
/-! PIN2 W9 (2026-11-11): twin of the release NHU_VerifyFrame (`stages`, `source`,
`parse_error`) over the PIN2 emission `PIN2_NEWGATE_verifyprefix` (namespace
`AspisR1PublicPreparationPIN2`, twin types), as PIN2_S1SemanticVerifyReachability did for
`verify_success`: statement text identical except the digest trait path
(`aspis_core.digest.Digest32`); the proof additionally unfolds the PCWN_NewLib
`branch`/`from_residual` the emission uses.  New module; the frozen one stays.
Release source: release-originals/NHU_VerifyFrame.lean (rebuilt against objs: identical up to
the embedded source path). -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparationPIN2
namespace AspisR1.PIN2_NHU_VerifyFrame
abbrev Wire := r1_wire.Error
abbrev Outcome (A : Type) := Result (core.result.Result A Wire)

def wireBind {A B : Type} (head : Outcome A) (next : A → Outcome B) : Outcome B := do
 let status ← head
 match status with
 | .Err e => ok (.Err e)
 | .Ok value => next value

def beginBind {H A : Type}
 (head : Result (core.result.Result aspis_core.state_only_prefix.r0.Challenges Wire × r1_wire.SemanticTranscript H))
 (next : aspis_core.state_only_prefix.r0.Challenges → r1_wire.SemanticTranscript H → Outcome A) : Outcome A := do
 let (status,after) ← head
 match status with
 | .Err e => ok (.Err e)
 | .Ok value => next value after

/-- Callee boundaries on the complete carrier (PIN2 twin of `NHU_VerifyFrame.stages`). -/
def stages (finish : VerifyPrefix.Finish) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H) :
 Outcome (r1_semantic.Verified H) :=
 wireBind (PrefixAdapter.parseAccepted bytes) (fun pre =>
 wireBind (r1_semantic.public_transcript D pub hash pre.c1_root) (fun initial =>
 beginBind (r1_wire.begin D pre initial) (fun challenges after =>
 finish D pub pre after challenges none)))

theorem source (finish : VerifyPrefix.Finish) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H) :
 VerifyPrefix.verify finish D pub bytes hash none = stages finish D pub bytes hash := by
 unfold VerifyPrefix.verify stages wireBind beginBind
 cases parsed : PrefixAdapter.parseAccepted bytes with
 | fail e => rfl
 | div => rfl
 | ok status =>
   cases status with
   | Err e =>
     simp only [bind_tc_ok, PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
       PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
       core.convert.FromSame.from]
   | Ok pre =>
     simp only [bind_tc_ok, VerifyPrefix.mark, PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch]
     cases created : r1_semantic.public_transcript D pub hash pre.c1_root with
     | fail e => rfl
     | div => rfl
     | ok status =>
       cases status with
       | Err e =>
         simp only [bind_tc_ok, PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch,
           PCWN_NewLib.core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
           core.convert.FromSame.from]
       | Ok initial =>
         simp only [bind_tc_ok, PCWN_NewLib.core.result.Result.Insts.CoreOpsTry.branch]
         cases begun : r1_wire.begin D pre initial with
         | fail e => rfl
         | div => rfl
         | ok pair => rcases pair with ⟨status,after⟩; cases status <;> rfl

/-- Every ambient and wire rejection before finish survives unchanged. -/
theorem parse_error (finish : VerifyPrefix.Finish) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
 (e : Wire) (rejected : PrefixAdapter.parseAccepted bytes=ok (.Err e)) :
 VerifyPrefix.verify finish D pub bytes hash none=ok (.Err e) := by
 rw [source]
 simp only [stages,rejected,wireBind,bind_tc_ok]

#print axioms source
#print axioms parse_error
end AspisR1.PIN2_NHU_VerifyFrame
