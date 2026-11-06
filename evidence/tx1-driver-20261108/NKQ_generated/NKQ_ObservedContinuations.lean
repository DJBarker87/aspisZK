import NKQ_ObservedStages
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_ObservedContinuations
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Out (H : Type) := NKQ_ObservedStages.Out H

def afterBegin (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (p : r1_wire.Prefix)
 (after : r1_wire.SemanticTranscript H) (r : core.result.Result r1_wire.Challenges r1_wire.Error) : Result (Out H) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue challenges => do
   VerifyPrefix.mark none 1#u8
   F D pub p after challenges none
 | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

def afterPublic (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (p : r1_wire.Prefix)
 (r : core.result.Result (r1_wire.SemanticTranscript H) r1_wire.Error) : Result (Out H) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue initial => do
   let (r2, after) ← r1_wire.begin D p initial
   afterBegin F D pub p after r2
 | .Break residual => core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual

theorem parsed_success (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (p : r1_wire.Prefix) :
 NKQ_ObservedStages.afterParsed F D pub hash (.Ok p) =
 (do let r ← r1_semantic.public_transcript D pub hash p.c1_root; afterPublic F D pub p r) := by rfl

theorem public_error (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (p : r1_wire.Prefix) (e : r1_wire.Error) :
 afterPublic F D pub p (.Err e) = ok (.Err e) := by rfl

theorem begin_error (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (p : r1_wire.Prefix)
 (after : r1_wire.SemanticTranscript H) (e : r1_wire.Error) :
 afterBegin F D pub p after (.Err e) = ok (.Err e) := by rfl

theorem finish_same_call (F : VerifyPrefix.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (p : r1_wire.Prefix)
 (after : r1_wire.SemanticTranscript H) (challenges : r1_wire.Challenges) :
 afterBegin F D pub p after (.Ok challenges) = F D pub p after challenges none := by rfl
#print axioms parsed_success
#print axioms public_error
#print axioms begin_error
#print axioms finish_same_call
#print finish_same_call
end AspisR1.NKQ_ObservedContinuations
end
