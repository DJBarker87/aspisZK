from pathlib import Path
import json
D=Path(__file__).parent
text='''import PV_DIAG9_Operands
set_option autoImplicit false
namespace PV_DIAG10
open PV_DIAG9
/-! A public environment does not supply witness-bearing operands, live PCs or
mutable logger state. All four independent field links remain explicit. -/
def PV_DIAG10_Link_Operands {I P : Type} (context : I → P)
 (calls : I → DiagnosticCall) : Prop :=
 ∀ i j, context i=context j → (calls i).operands=(calls j).operands
def PV_DIAG10_Link_Sites {I P : Type} (context : I → P)
 (calls : I → DiagnosticCall) : Prop :=
 ∀ i j, context i=context j → (calls i).site=(calls j).site
def PV_DIAG10_Link_Frames {I P : Type} (context : I → P)
 (calls : I → DiagnosticCall) : Prop :=
 ∀ i j, context i=context j → (calls i).frames=(calls j).frames
def PV_DIAG10_Link_Levels {I P : Type} (context : I → P)
 (calls : I → DiagnosticCall) : Prop :=
 ∀ i j, context i=context j → (calls i).level=(calls j).level
'''
steps=[('call_fields_suffice','''theorem call_fields_suffice (a b : DiagnosticCall)
 (site : a.site=b.site) (operands : a.operands=b.operands)
 (frames : a.frames=b.frames) (level : a.level=b.level) : a=b := by
 cases a
 cases b
 cases site
 cases operands
 cases frames
 cases level
 rfl'''),
('public_call_from_links','''theorem public_call_from_links {I P : Type} (context : I → P)
 (calls : I → DiagnosticCall) (sites : PV_DIAG10_Link_Sites context calls)
 (operands : PV_DIAG10_Link_Operands context calls)
 (frames : PV_DIAG10_Link_Frames context calls) (levels : PV_DIAG10_Link_Levels context calls)
 (i j : I) (h : context i=context j) : calls i=calls j :=
 call_fields_suffice _ _ (sites i j h) (operands i j h) (frames i j h) (levels i j h)'''),
('selected_returned_call_restoration','''theorem selected_returned_call_restoration (site level : Nat) (operands : List String)
 (a b : LivePath) (f g : Nat) (caller : Stack) :
 DiagnosticCall.mk site operands (pathRun (.call f a) caller).2 level =
 DiagnosticCall.mk site operands (pathRun (.call g b) caller).2 level :=
 returned_error_callsite_frames site level operands a b f g caller'''),
('native_frame_binding_transport','''theorem native_frame_binding_transport {Cfg PC : Type} (encode : Cfg → Stack → PC)
 (cfg : Cfg) (a b : LivePath) (f g : Nat) (caller : Stack) :
 encode cfg (pathRun (.call f a) caller).2=encode cfg (pathRun (.call g b) caller).2 := by
 rw [normal_return_restores,normal_return_restores]'''),
('format_dynamic_operands','''theorem format_dynamic_operands {I P O : Type} (context : I → P)
 (calls : I → DiagnosticCall) (operands : PV_DIAG10_Link_Operands context calls)
 (render : List String → O) (i j : I) (h : context i=context j) :
 render (calls i).operands=render (calls j).operands :=
 format_operands_transport render _ _ (operands i j h)'''),
('format_dynamic_lengths','''theorem format_dynamic_lengths {I P : Type} (context : I → P)
 (calls : I → DiagnosticCall) (operands : PV_DIAG10_Link_Operands context calls)
 (i j : I) (h : context i=context j) : operandLengths (calls i)=operandLengths (calls j) :=
 format_operand_byte_lengths _ _ (operands i j h)'''),
('format_dynamic_capacity','''theorem format_dynamic_capacity {I P : Type} (context : I → P)
 (calls : I → DiagnosticCall) (operands : PV_DIAG10_Link_Operands context calls)
 (capacity : List Nat → Nat) (i j : I) (h : context i=context j) :
 capacity (operandLengths (calls i))=capacity (operandLengths (calls j)) :=
 formatter_capacity_transport capacity _ _ (operands i j h)'''),
('formatter_environment_and_operands','''theorem formatter_environment_and_operands {Cfg O : Type}
 (render : Cfg → List String → O) (cfg cfg2 : Cfg) (a b : DiagnosticCall)
 (environment : cfg=cfg2) (operands : a.operands=b.operands) :
 render cfg a.operands=render cfg2 b.operands := by rw [environment,operands]'''),
('logger_reply_with_state','''theorem logger_reply_with_state {Cfg : Type}
 (dispatch : Cfg → Nat → DiagnosticCall → DiagnosticReply) (cfg : Cfg)
 (s t : Nat) (a b : DiagnosticCall) (state : s=t) (call : a=b) :
 dispatch cfg s a=dispatch cfg t b := by rw [state,call]'''),
('logger_joint_trace','''theorem logger_joint_trace {Cfg : Type}
 (dispatch : Cfg → Nat → DiagnosticCall → DiagnosticReply) (cfg : Cfg)
 (s t : Nat) (a b : List DiagnosticCall) (state : s=t) (calls : a=b) :
 dispatchCalls dispatch cfg s a=dispatchCalls dispatch cfg t b :=
 logger_trace_transport dispatch cfg s t a b state calls'''),
('logger_final_state_retained','''theorem logger_final_state_retained {Cfg : Type}
 (dispatch : Cfg → Nat → DiagnosticCall → DiagnosticReply) (cfg : Cfg)
 (s t : Nat) (a b : List DiagnosticCall) (state : s=t) (calls : a=b) :
 (dispatchCalls dispatch cfg s a).2=(dispatchCalls dispatch cfg t b).2 :=
 congrArg Prod.snd (logger_joint_trace dispatch cfg s t a b state calls)'''),
('logger_failure_prefix_retained','''theorem logger_failure_prefix_retained {Cfg : Type}
 (dispatch : Cfg → Nat → DiagnosticCall → DiagnosticReply) (cfg : Cfg)
 (s : Nat) (c : DiagnosticCall) (tail : List DiagnosticCall) :
 (dispatchCalls dispatch cfg s (c::tail)).1.head?=some (dispatch cfg s c) :=
 logger_failure_not_erased dispatch cfg s c tail'''),
('earlier_captures_required','''theorem earlier_captures_required (a b : LivePath) (f g : Nat) (caller : Stack)
 (enabled : Bool) (earlier : (pathRun a (f::caller)).1=(pathRun b (g::caller)).1) :
 (afterReturn a f caller enabled).1=(afterReturn b g caller enabled).1 :=
 complete_capture_transport a b f g caller enabled earlier'''),
('selected_capture_does_not_erase_prefix','''theorem selected_capture_does_not_erase_prefix (a : LivePath) (f : Nat) (caller : Stack) :
 (afterReturn a f caller true).1=(pathRun a (f::caller)).1++[caller] :=
 earlier_captures_retained a f caller'''),
('same_logger_config_not_operand_law','''theorem same_logger_config_not_operand_law :
 (DiagnosticCall.mk 0 ["0"] [] 0).site=(DiagnosticCall.mk 0 ["1"] [] 0).site ∧
 (DiagnosticCall.mk 0 ["0"] [] 0).operands ≠ (DiagnosticCall.mk 0 ["1"] [] 0).operands := by
 constructor
 · rfl
 · decide''')]
plans=[]
for name,decl in steps:
 text+=decl+'\n#print axioms '+name+'\n';plans.append(text+'end PV_DIAG10\n')
(D/'operands-plans.json').write_text(json.dumps({'PV_DIAG10_Operands':plans},indent=2)+'\n')
(D/'PV_DIAG10_Operands.lean').write_text(plans[-1])
