import LIBB_ModelGraph
import LIBB_PoolEncode
import NFY_Part058
set_option autoImplicit false
namespace LIBB_PoolEmit
open Aeneas Aeneas.Std
abbrev State := AspisR1.S2I.ReturnData.State Unit Empty
def initial : State := ⟨(),[],[]⟩
def runtime (s : State) (b : List U8) : Result State := .ok (AspisR1.S2I.ReturnData.set s b)
/-- RuntimeReturnData is the already retained runtime row. Its exact byte
argument and event order survive in this deterministic model. -/
def code (s : LIBB_PoolCarriers.Statement) :=
 AspisR1.NFY_JHb_Emit.source runtime initial (LIBB_PoolEncode.terminal s)
def event : AspisR1.S2I.ReturnData.Event Empty → RSL.Event
 | .setReturnData b => .returnData (NNC_ByteCarriers.host b)
 | .other impossible => nomatch impossible

def observation (s : LIBB_PoolCarriers.Statement) : RSL.Obs (Except RSL.ProgramError Unit) :=
 match code s with
 | .ok (.Ok st) => ⟨.ret (.ok ()),st.events.map event⟩
 | .ok (.Err e) => ⟨.ret (.error (NMS_R2N_RSLError.error e)),[]⟩
 | .fail _ => ⟨.abort,[]⟩
 | .div => ⟨.diverge,[]⟩
def emitResult (s : LIBB_PoolCarriers.Statement) : RSL.RS Unit := fun _ o => o = observation s
def evaluator (s : LIBB_PoolCarriers.Statement) : Except RSL.ProgramError Unit :=
 match (observation s).exit with | .ret r => r | _ => .error .invalidInstructionData

/-- CLOSED219 root, at the SAME original statement carrier conversion. -/
theorem root (s : LIBB_PoolCarriers.Statement) :
 NFY_NEU_EmitModel.run
   AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_result_against_statement_v1
   NFY_NEY_EmitComposed.encode runtime initial (LIBB_PoolEncode.terminal s) = code s :=
 NFY_NEY_EmitComposed.result_state_effects initial (LIBB_PoolEncode.terminal s)

theorem returns (s : LIBB_PoolCarriers.Statement) (env : RSL.Env) :
 NND_Returned.Returns (emitResult s) env (evaluator s) := by
 intro o r h hr
 subst o
 unfold evaluator
 rw [hr]
 rfl

theorem returned_event (st : State) (b : List U8) :
 (AspisR1.S2I.ReturnData.set st b).events.map event =
 st.events.map event ++ [.returnData (NNC_ByteCarriers.host b)] := by
 simp only [AspisR1.S2I.ReturnData.set,List.map_append,List.map_cons,List.map_nil,event]
#print axioms root
#print axioms returns
#print axioms returned_event
end LIBB_PoolEmit
