from pathlib import Path
import json
D=Path(__file__).parent;m='PV_DIAG9_Frames'
s='''import PV_DIAG9_Result
set_option autoImplicit false
namespace PV_DIAG9
/-! Normal call/return stack restoration. Internal captures are retained.
A native association must establish these are normal returns at the selected
map_err call, and that PCs/inlining/unwinder state implement this stack. -/
inductive LivePath
 | done
 | capture (enabled : Bool)
 | seq (first second : LivePath)
 | call (frame : Nat) (body : LivePath)
 deriving DecidableEq
abbrev Stack := List Nat
abbrev Captures := List Stack
def pathRun : LivePath → Stack → Captures × Stack
 | .done,s => ([],s)
 | .capture enabled,s => (if enabled then [s] else [],s)
 | .seq first second,s =>
   let a := pathRun first s
   let b := pathRun second a.2
   (a.1++b.1,b.2)
 | .call f body,s =>
   let a := pathRun body (f::s)
   (a.1,a.2.tail)
def afterReturn (body : LivePath) (callee : Nat) (caller : Stack) (enabled : Bool) :=
 pathRun (.seq (.call callee body) (.capture enabled)) caller
'''
steps=[('normal_return_restores','''theorem normal_return_restores (path : LivePath) (s : Stack) :
 (pathRun path s).2=s := by
 induction path generalizing s with
 | done => rfl
 | capture enabled => rfl
 | seq first second ih1 ih2 =>
   change (pathRun second (pathRun first s).2).2=s
   rw [ih2,ih1]
 | call f body ih =>
   change (pathRun body (f::s)).2.tail=s
   rw [ih]; rfl'''),
('caller_capture_after_return','''theorem caller_capture_after_return (body : LivePath) (f : Nat) (s : Stack) (enabled : Bool) :
 (afterReturn body f s enabled).1 =
 (pathRun body (f::s)).1 ++ (if enabled then [s] else []) := by
 change (pathRun body (f::s)).1 ++ (if enabled then [(pathRun body (f::s)).2.tail] else []) = _
 rw [normal_return_restores]
 rfl'''),
('callee_frames_not_live_after_return','''theorem callee_frames_not_live_after_return (body : LivePath) (f : Nat) (s : Stack) :
 (pathRun (.call f body) s).2=s := normal_return_restores _ _'''),
('returned_error_frames','''theorem returned_error_frames {E : Type} (error : E) (body : LivePath) (f : Nat) (s : Stack) :
 (fun _ : E => (pathRun (.call f body) s).2) error=s := normal_return_restores _ _'''),
('different_retry_paths_same_live_stack','''theorem different_retry_paths_same_live_stack (a b : LivePath) (f g : Nat) (s : Stack) :
 (pathRun (.call f a) s).2=(pathRun (.call g b) s).2 := by
 rw [normal_return_restores,normal_return_restores]'''),
('selected_capture_public_after_return','''theorem selected_capture_public_after_return (a b : LivePath) (f g : Nat) (s : Stack)
 (enabled : Bool) :
 (if enabled then [(pathRun (.call f a) s).2] else []) =
 (if enabled then [(pathRun (.call g b) s).2] else []) := by
 rw [normal_return_restores,normal_return_restores]'''),
('earlier_captures_retained','''theorem earlier_captures_retained (body : LivePath) (f : Nat) (s : Stack) :
 (afterReturn body f s true).1=(pathRun body (f::s)).1++[s] :=
 caller_capture_after_return body f s true'''),
('disabled_selected_capture_retains_prefix','''theorem disabled_selected_capture_retains_prefix (body : LivePath) (f : Nat) (s : Stack) :
 (afterReturn body f s false).1=(pathRun body (f::s)).1 := by
 rw [caller_capture_after_return]; exact List.append_nil _'''),
('capture_free_done','''theorem capture_free_done (s : Stack) : (pathRun .done s).1=[] := rfl'''),
('capture_free_call','''theorem capture_free_call (body : LivePath) (f : Nat) (s : Stack)
 (h : (pathRun body (f::s)).1=[]) : (pathRun (.call f body) s).1=[] := h'''),
('capture_free_seq','''theorem capture_free_seq (a b : LivePath) (s : Stack)
 (ha : (pathRun a s).1=[]) (hb : (pathRun b s).1=[]) :
 (pathRun (.seq a b) s).1=[] := by
 change (pathRun a s).1++(pathRun b (pathRun a s).2).1=[]
 rw [normal_return_restores,ha,hb]; rfl'''),
('normal_returns_do_not_erase_internal_captures','''theorem normal_returns_do_not_erase_internal_captures :
 (afterReturn (.capture true) 1 [] true).1 ≠
 (afterReturn (.capture true) 2 [] true).1 := by decide'''),
('public_selected_capture_decoder','''theorem public_selected_capture_decoder {O : Type} (decode : Captures → O)
 (a b : LivePath) (f g : Nat) (s : Stack) (enabled : Bool) :
 decode (if enabled then [(pathRun (.call f a) s).2] else []) =
 decode (if enabled then [(pathRun (.call g b) s).2] else []) :=
 congrArg decode (selected_capture_public_after_return a b f g s enabled)'''),
('complete_capture_transport','''theorem complete_capture_transport (a b : LivePath) (f g : Nat) (s : Stack) (enabled : Bool)
 (capturedPrefix : (pathRun a (f::s)).1=(pathRun b (g::s)).1) :
 (afterReturn a f s enabled).1=(afterReturn b g s enabled).1 := by
 rw [caller_capture_after_return,caller_capture_after_return,capturedPrefix]''')]
cs=[]
for n,d in steps:s+=d+'\n#print axioms '+n+'\n';cs.append(s+'end PV_DIAG9\n')
j=json.loads((D/'plans.json').read_text());j[m]=cs;(D/'plans.json').write_text(json.dumps(j,indent=2)+'\n');(D/(m+'.lean')).write_text(cs[-1])
