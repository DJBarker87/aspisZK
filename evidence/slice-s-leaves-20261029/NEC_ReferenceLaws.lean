import NEC_EmitRef.Funs
import NEC_BindingRef.Funs
import NEC_EmitModel
import NEC_ResultCaller
set_option autoImplicit false
namespace NEC_ReferenceLaws
open Aeneas Aeneas.Std Result

def emit (validation encoded magic : Bool) : core.result.Result Unit U8 :=
 if validation && encoded && magic then .Ok () else .Err 0#u8

theorem emit_total (validation encoded magic : Bool) :
 NEC_EmitRef.emit_ref validation encoded magic=ok (emit validation encoded magic) := by
 cases validation <;> cases encoded <;> cases magic <;> rfl

def binding {E : Type} (first second : core.result.Result Unit E) (mismatch : Bool) (error : E) :
 core.result.Result Unit E := match first with
 | .Err error=>.Err error
 | .Ok _=>match second with
   | .Err error=>.Err error
   | .Ok _=>if mismatch then .Err error else .Ok ()

theorem binding_total {E : Type} (first second : core.result.Result Unit E)
 (mismatch : Bool) (error : E) :
 NEC_BindingRef.binding_ref first second mismatch error=ok (binding first second mismatch error) := by
 cases first <;> cases second <;> cases mismatch <;> rfl

def classify {A : Type} (reply : core.result.Result A NEC_EmitModel.ProgramError) : core.result.Result Unit U8 :=
 match reply with | .Ok _=>.Ok () | .Err _=>.Err 0#u8

/-- Classification accompanies, and does not erase, the explicit returned
runtime state. It does not assert that the native op53 frame is instantiated. -/
theorem runtime_projection {A E : Type}
 (runtime : AspisR1.S2I.ReturnData.State A E → List U8 → Result (AspisR1.S2I.ReturnData.State A E))
 (runtimeLaw : AspisR1.S2I.ReturnData.RuntimePremise runtime)
 (state : AspisR1.S2I.ReturnData.State A E) (statement : NEC_EmitModel.Statement) (bytes : Array U8 792#usize)
 (first : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1 statement (NEC_EmitModel.derived statement)=ok (.Ok ()))
 (second : AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.encode_pool_v1_pair_forest_terminal_result_v1 (NEC_EmitModel.derived statement)=ok (.Ok bytes))
 (magic : bytes.val.take 4=[65#u8,83#u8,82#u8,56#u8]) :
 AspisR1.JHb_Emit.source runtime state statement=ok (.Ok (AspisR1.S2I.ReturnData.set state bytes.val)) ∧
 (do let reply ← AspisR1.JHb_Emit.source runtime state statement
     ok (classify reply))=NEC_EmitRef.emit_ref true true true := by
 have h := NEC_EmitModel.runtime_output runtime runtimeLaw state statement bytes first second magic
 refine ⟨h,?_⟩
 rw [h]
 rfl

#print axioms emit_total
#print axioms binding_total
#print axioms runtime_projection
end NEC_ReferenceLaws
