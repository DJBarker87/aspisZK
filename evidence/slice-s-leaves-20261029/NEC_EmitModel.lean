import JHb_Emit
set_option autoImplicit false
noncomputable section
namespace NEC_EmitModel
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_forest_terminal
abbrev Statement := AspisR1.S2K.StatementAdmission.Statement
abbrev Output := PoolV1PairForestTerminalResultV1
abbrev Error := PoolV1PairForestTerminalFormatErrorV1
abbrev derived := AspisR1.S2K.ResultAdmission.value
abbrev ProgramError := AdapterRw.solana_program_error.ProgramError

def erase {A E : Type} (reply : core.result.Result (AspisR1.S2I.ReturnData.State A E) ProgramError) :
 core.result.Result Unit ProgramError := match reply with | .Ok _=>.Ok () | .Err e=>.Err e

theorem validation_error {A E : Type}
 (runtime : AspisR1.S2I.ReturnData.State A E → List U8 → Result (AspisR1.S2I.ReturnData.State A E))
 (state : AspisR1.S2I.ReturnData.State A E) (statement : Statement) (error : Error)
 (child : validate_pool_v1_pair_forest_terminal_result_against_statement_v1 statement (derived statement)=ok (.Err error)) :
 AspisR1.JHb_Emit.source runtime state statement=ok (.Err .InvalidInstructionData) := by
 unfold AspisR1.JHb_Emit.source
 dsimp only
 rw [child]
 rfl

theorem encode_error {A E : Type}
 (runtime : AspisR1.S2I.ReturnData.State A E → List U8 → Result (AspisR1.S2I.ReturnData.State A E))
 (state : AspisR1.S2I.ReturnData.State A E) (statement : Statement) (error : Error)
 (first : validate_pool_v1_pair_forest_terminal_result_against_statement_v1 statement (derived statement)=ok (.Ok ()))
 (second : encode_pool_v1_pair_forest_terminal_result_v1 (derived statement)=ok (.Err error)) :
 AspisR1.JHb_Emit.source runtime state statement=ok (.Err .InvalidInstructionData) := by
 unfold AspisR1.JHb_Emit.source
 dsimp only
 rw [first,bind_tc_ok,second]
 rfl

theorem runtime_output {A E : Type}
 (runtime : AspisR1.S2I.ReturnData.State A E → List U8 → Result (AspisR1.S2I.ReturnData.State A E))
 (runtimeLaw : AspisR1.S2I.ReturnData.RuntimePremise runtime)
 (state : AspisR1.S2I.ReturnData.State A E) (statement : Statement) (bytes : Array U8 792#usize)
 (first : validate_pool_v1_pair_forest_terminal_result_against_statement_v1 statement (derived statement)=ok (.Ok ()))
 (second : encode_pool_v1_pair_forest_terminal_result_v1 (derived statement)=ok (.Ok bytes))
 (magic : bytes.val.take 4=[65#u8,83#u8,82#u8,56#u8]) :
 AspisR1.JHb_Emit.source runtime state statement=ok (.Ok (AspisR1.S2I.ReturnData.set state bytes.val)) := by
 unfold AspisR1.JHb_Emit.source
 dsimp only
 rw [first,bind_tc_ok,second,bind_tc_ok]
 dsimp only
 rw [if_neg (by exact not_not_intro bytes.property)]
 rw [if_neg (by exact not_not_intro magic)]
 rw [runtimeLaw,bind_tc_ok]

theorem bad_magic {A E : Type}
 (runtime : AspisR1.S2I.ReturnData.State A E → List U8 → Result (AspisR1.S2I.ReturnData.State A E))
 (state : AspisR1.S2I.ReturnData.State A E) (statement : Statement) (bytes : Array U8 792#usize)
 (first : validate_pool_v1_pair_forest_terminal_result_against_statement_v1 statement (derived statement)=ok (.Ok ()))
 (second : encode_pool_v1_pair_forest_terminal_result_v1 (derived statement)=ok (.Ok bytes))
 (magic : bytes.val.take 4≠[65#u8,83#u8,82#u8,56#u8]) :
 AspisR1.JHb_Emit.source runtime state statement=ok (.Err .InvalidInstructionData) := by
 unfold AspisR1.JHb_Emit.source
 dsimp only
 rw [first,bind_tc_ok,second,bind_tc_ok]
 dsimp only
 rw [if_neg (by exact not_not_intro bytes.property),if_pos magic]

#print axioms validation_error
#print axioms encode_error
#print axioms runtime_output
#print axioms bad_magic
end NEC_EmitModel
end
