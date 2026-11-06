import NKA_FinishTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_ObservedStages
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Out (H : Type) := core.result.Result (r1_semantic.Verified H) r1_wire.Error

/-- Source continuation following the SAME Prefix::parse reply. No native
certificate, child-law assumption or closure credit is asserted by this definition. -/
def afterParsed (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H)
 (r : core.result.Result r1_wire.Prefix r1_wire.Error) : Result (Out H) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue p => do
   VerifyPrefix.mark none 0#u8
   let r1 ← r1_semantic.public_transcript D pub hash p.c1_root
   let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
   match cf1 with
   | .Continue initial => do
     let (r2, afterBegin) ← r1_wire.begin D p initial
     let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
     match cf2 with
     | .Continue challenges => do
       VerifyPrefix.mark none 1#u8
       F D pub p afterBegin challenges none
     | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
   | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual
 | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

theorem factor (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H) :
 VerifyPrefix.verify F D pub bytes hash none =
 (do let r ← PrefixAdapter.parseAccepted bytes; afterParsed F D pub hash r) := by rfl

theorem parsed_error (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (e : r1_wire.Error) :
 afterParsed F D pub hash (.Err e) = ok (.Err e) := by rfl

/-- Complete outer abort prefixes: no finish or later transcript is evaluated. -/
theorem parsed_fail (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (e : Error) :
 (do let r ← (Result.fail e : Result (core.result.Result r1_wire.Prefix r1_wire.Error))
     afterParsed F D pub hash r) = (.fail e : Result (Out H)) := by rfl

theorem parsed_div (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) :
 (do let r ← (Result.div : Result (core.result.Result r1_wire.Prefix r1_wire.Error))
     afterParsed F D pub hash r) = (.div : Result (Out H)) := by rfl
#print axioms factor
#print axioms parsed_error
#print axioms parsed_fail
#print axioms parsed_div
#print factor
end AspisR1.NKQ_ObservedStages
end
