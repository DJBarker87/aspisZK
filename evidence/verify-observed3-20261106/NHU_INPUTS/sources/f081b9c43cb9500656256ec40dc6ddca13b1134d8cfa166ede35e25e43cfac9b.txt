import NHU_Mark
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
namespace AspisR1.NHU_VerifyFrame
abbrev Wire := r1_wire.Error
abbrev Outcome (A : Type) := Result (core.result.Result A Wire)

def wireBind {A B : Type} (head : Outcome A) (next : A → Outcome B) : Outcome B := do
 let status ← head
 match status with
 | .Err e => ok (.Err e)
 | .Ok value => next value

def beginBind {H A : Type}
 (head : Result (core.result.Result r1_wire.Challenges Wire × r1_wire.SemanticTranscript H))
 (next : r1_wire.Challenges → r1_wire.SemanticTranscript H → Outcome A) : Outcome A := do
 let (status,after) ← head
 match status with
 | .Err e => ok (.Err e)
 | .Ok value => next value after

/-- Callee boundaries on the complete carrier. This is a model equation;
it supplies no native driver or missing finish packet. -/
def stages (finish : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H) :
 Outcome (r1_semantic.Verified H) :=
 wireBind (PrefixAdapter.parseAccepted bytes) (fun pre =>
 wireBind (r1_semantic.public_transcript D pub hash pre.c1_root) (fun initial =>
 beginBind (r1_wire.begin D pre initial) (fun challenges after =>
 finish D pub pre after challenges none)))

theorem source (finish : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H) :
 VerifyPrefix.verify finish D pub bytes hash none = stages finish D pub bytes hash := by
 unfold VerifyPrefix.verify stages wireBind beginBind
 cases parsed : PrefixAdapter.parseAccepted bytes with
 | fail e => rfl
 | div => rfl
 | ok status =>
   cases status with
   | Err e => rfl
   | Ok pre =>
     simp only [bind_tc_ok, VerifyPrefix.mark, core.result.Result.Insts.CoreOpsTry.branch]
     cases created : r1_semantic.public_transcript D pub hash pre.c1_root with
     | fail e => rfl
     | div => rfl
     | ok status =>
       cases status with
       | Err e => rfl
       | Ok initial =>
         simp only [bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch]
         cases begun : r1_wire.begin D pre initial with
         | fail e => rfl
         | div => rfl
         | ok pair => rcases pair with ⟨status,after⟩; cases status <;> rfl

/-- Every ambient and wire rejection before finish survives unchanged. -/
theorem parse_error (finish : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H)
 (e : Wire) (rejected : PrefixAdapter.parseAccepted bytes=ok (.Err e)) :
 VerifyPrefix.verify finish D pub bytes hash none=ok (.Err e) := by
 rw [source]
 simp only [stages,rejected,wireBind,bind_tc_ok]

#print axioms source
#print axioms parse_error
end AspisR1.NHU_VerifyFrame
