import NGX_CodeTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode
namespace AspisR1.NGX_NewTrace
abbrev Bytes32 := Array U8 32#usize

theorem returned {H : Type} (D : aspis_core.Digest32 H) (hash : H)
 (pub : Slice U8) (root reply : Bytes32)
 (bound : (Slice.len pub).val≤4294967295)
 (digest : D.digest hash (NGX_SemanticNew.parts pub root (UScalar.cast .U32 (Slice.len pub)))=ok reply) :
 run (S1SemanticCode.newTranscript D hash pub root)=
 ([Event.digest D hash (NGX_SemanticNew.parts pub root (UScalar.cast .U32 (Slice.len pub))) (ok reply)],
  ok (.Ok {state:=reply,hash,next_row:=0#u8})) := by
 unfold S1SemanticCode.newTranscript
 simp only [NGX_SemanticNew.parts] at digest ⊢
 simp only [NGX_SemanticNew.length_success _ bound,NGX_CodeTrace.lift_bind,
  AspisR1PublicPreparation.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
  lift,NGX_CodeTrace.digest_bind,NGX_CodeTrace.pure_run,digest]

theorem rejected {H : Type} (D : aspis_core.Digest32 H) (hash : H)
 (pub : Slice U8) (root : Bytes32) (bound : 4294967295<(Slice.len pub).val) :
 run (S1SemanticCode.newTranscript D hash pub root)=([],ok (.Err .Public)) := by
 have mapping : AspisR1PublicPreparation.core.result.Result.map_err
  (r1_wire.SemanticTranscript.new.closure.Insts.CoreOpsFunctionFnOnceTupleTryFromIntErrorError D)
  (.Err ()) ()=ok (.Err r1_wire.Error.Public) := by rfl
 unfold S1SemanticCode.newTranscript
 simp only [NGX_SemanticNew.length_error _ bound,NGX_CodeTrace.lift_bind,mapping,
  core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
  core.convert.FromSame.from,NGX_CodeTrace.lift_run]
#print axioms returned
#print axioms rejected
end AspisR1.NGX_NewTrace
