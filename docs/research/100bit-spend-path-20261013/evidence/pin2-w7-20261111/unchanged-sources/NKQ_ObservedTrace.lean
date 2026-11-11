import NKQ_ObservedContinuations
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKQ_ObservedTrace
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
abbrev Out (H : Type) := NKQ_ObservedStages.Out H
open PreparedHashCode (Code run)

def afterParsed (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H)
 (r : core.result.Result r1_wire.Prefix r1_wire.Error) : Code (Out H) := do
 let cf ← core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | .Continue p => do
   VerifyPrefix.mark none 0#u8
   let r1 ← S1SemanticCode.publicTranscript D pub hash p.c1_root
   let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
   match cf1 with
   | .Continue initial => do
     let (r2, afterBegin) ← S1SemanticCode.begin D p initial
     let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
     match cf2 with
     | .Continue challenges => do
       VerifyPrefix.mark none 1#u8
       F D pub p afterBegin challenges none
     | .Break residual => liftM (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual)
   | .Break residual => liftM (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual)
 | .Break residual => liftM (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual (r1_semantic.Verified H) (core.convert.FromSame r1_wire.Error) residual)

theorem factor (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (bytes : Slice U8) (hash : H) :
 S1SemanticCode.verify F D pub bytes hash none =
 (do let r ← liftM (PrefixAdapter.parseAccepted bytes);afterParsed F D pub hash r) := by rfl

theorem parser_rejection (F : S1SemanticCode.Finish) {H : Type} (D : aspis_core.Digest32 H)
 (pub : pool_v1.pair_forest_semantic_terminal.r0.Public) (hash : H) (e : r1_wire.Error) :
 run (afterParsed F D pub hash (.Err e))=([],ok (.Err e)) := by rfl
#print axioms factor
#print axioms parser_rejection
#print factor
end AspisR1.NKQ_ObservedTrace
end
