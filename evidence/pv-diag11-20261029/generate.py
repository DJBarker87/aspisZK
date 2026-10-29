from pathlib import Path
import json
D=Path(__file__).resolve().parent
plans={}
def module(name,imports,defs,ths):
 head='\n'.join('import '+x for x in imports)+'\nset_option autoImplicit false\nnamespace PV_DIAG11\n'+defs+'\n'
 out=[]
 for n,stmt,proof in ths:
  head+='theorem '+n+' '+stmt+' := '+proof+'\n#print axioms '+n+'\n'
  out.append(head+'end PV_DIAG11\n')
 plans['PV_DIAG11_'+name]=out
 (D/('PV_DIAG11_'+name+'.lean')).write_text(out[-1])
module('Execution',['Init'],r'''
/-! Source control combinators, with primitive call traces retained. This is
not a deployed instance; primitive call bodies and unwinding are not axiomatized.
A halted leaf carries its complete finite prefix, including cleanup effects. -/
inductive Exit (E A : Type) where
 | ok (value : A) | error (value : E) | panic | oom | abort | diverge
 deriving DecidableEq, Repr
structure Run (V E A : Type) where
 events : List V
 exit : Exit E A
 deriving Repr
def ret {V E A : Type} (a : A) : Run V E A := ⟨[],.ok a⟩
def pre {V E A : Type} (xs : List V) (r : Run V E A) : Run V E A := ⟨xs++r.events,r.exit⟩
def seq {V E A B : Type} (r : Run V E A) (f : A → Run V E B) : Run V E B :=
 match r.exit with
 | .ok a => pre r.events (f a)
 | .error e => ⟨r.events,.error e⟩
 | .panic => ⟨r.events,.panic⟩
 | .oom => ⟨r.events,.oom⟩
 | .abort => ⟨r.events,.abort⟩
 | .diverge => ⟨r.events,.diverge⟩
def mapError {V E F A : Type} (f : E → F) (r : Run V E A) : Run V F A :=
 ⟨r.events,match r.exit with
 | .ok a => .ok a | .error e => .error (f e) | .panic => .panic
 | .oom => .oom | .abort => .abort | .diverge => .diverge⟩
''',[
('pre_empty','{V E A : Type} (r : Run V E A) : pre [] r=r','by cases r; simp only [pre,List.nil_append]'),
('pre_assoc','{V E A : Type} (xs ys : List V) (r : Run V E A) : pre xs (pre ys r)=pre (xs++ys) r','by cases r; simp only [pre,List.append_assoc]'),
('seq_ok','{V E A B : Type} (xs : List V) (a : A) (f : A → Run V E B) : seq ⟨xs,.ok a⟩ f=pre xs (f a)','rfl'),
('seq_error','{V E A B : Type} (xs : List V) (e : E) (f : A → Run V E B) : seq ⟨xs,.error e⟩ f=⟨xs,.error e⟩','rfl'),
('seq_panic','{V E A B : Type} (xs : List V) (f : A → Run V E B) : seq ⟨xs,.panic⟩ f=⟨xs,.panic⟩','rfl'),
('seq_oom','{V E A B : Type} (xs : List V) (f : A → Run V E B) : seq ⟨xs,.oom⟩ f=⟨xs,.oom⟩','rfl'),
('seq_abort','{V E A B : Type} (xs : List V) (f : A → Run V E B) : seq ⟨xs,.abort⟩ f=⟨xs,.abort⟩','rfl'),
('seq_diverge','{V E A B : Type} (xs : List V) (f : A → Run V E B) : seq ⟨xs,.diverge⟩ f=⟨xs,.diverge⟩','rfl'),
('seq_ret','{V E A B : Type} (a : A) (f : A → Run V E B) : seq (ret a) f=f a','by exact pre_empty (f a)'),
('seq_prefix','{V E A B : Type} (r : Run V E A) (f : A → Run V E B) : ∃ xs, (seq r f).events=r.events++xs','by cases r with | mk es ex => cases ex <;> simp only [seq,pre] <;> first | exact ⟨_,rfl⟩ | exact ⟨[],(List.append_nil _).symm⟩'),
('seq_assoc','{V E A B C : Type} (r : Run V E A) (f : A → Run V E B) (g : B → Run V E C) : seq (seq r f) g=seq r (fun a => seq (f a) g)','by
 cases r with
 | mk es ex =>
   cases ex with
   | ok a =>
     cases h : f a with
     | mk fs fx => cases fx <;> simp only [seq,pre,h,List.append_assoc]
   | error e => rfl
   | panic => rfl
   | oom => rfl
   | abort => rfl
   | diverge => rfl'),
('map_error_prefix','{V E F A : Type} (f : E → F) (r : Run V E A) : (mapError f r).events=r.events','rfl'),
])
module('WriteAll',['PV_DIAG11_Execution'],r'''
/-! Rust 1.94.1 std::io::Write::write_all branch interpreter.
Fuel bounds observations, NOT source termination: zero fuel on nonempty input
is a divergent finite prefix. Every write call's own effects are retained.
The primitive must implement the Write contract (including count <= length).
An invalid count exposes a panic rather than saturating the slice operation. -/
inductive IoError where | interrupted | writeZero | other (code : Nat)
 deriving DecidableEq, Repr
def writeAll {V : Type} (write : List UInt8 → Run V IoError Nat) :
 Nat → List UInt8 → Run V IoError Unit
 | _,[] => ret ()
 | 0,_::_ => ⟨[],.diverge⟩
 | fuel+1,buf@(_::_) =>
   let r := write buf
   match r.exit with
   | .ok 0 => ⟨r.events,.error .writeZero⟩
   | .ok (n+1) => if n+1 ≤ buf.length then pre r.events (writeAll write fuel (buf.drop (n+1))) else ⟨r.events,.panic⟩
   | .error .interrupted => pre r.events (writeAll write fuel buf)
   | .error e => ⟨r.events,.error e⟩
   | .panic => ⟨r.events,.panic⟩ | .oom => ⟨r.events,.oom⟩
   | .abort => ⟨r.events,.abort⟩ | .diverge => ⟨r.events,.diverge⟩
''',[
('writeAll_empty','{V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) : writeAll w fuel []=ret ()','by cases fuel <;> rfl'),
('writeAll_prefix_cut','{V : Type} (w : List UInt8 → Run V IoError Nat) (b : UInt8) (bs : List UInt8) : writeAll w 0 (b::bs)=⟨[],.diverge⟩','rfl'),
('writeAll_zero','{V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.ok 0⟩) : writeAll w (fuel+1) (b::bs)=⟨es,.error .writeZero⟩','by simp only [writeAll,h]'),
('writeAll_interrupted','{V : Type} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.error .interrupted⟩) : writeAll w (fuel+1) (b::bs)=pre es (writeAll w fuel (b::bs))','by simp only [writeAll,h]'),
('writeAll_other_error','{V : Type} (w : List UInt8 → Run V IoError Nat) (fuel code : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.error (.other code)⟩) : writeAll w (fuel+1) (b::bs)=⟨es,.error (.other code)⟩','by simp only [writeAll,h]'),
('writeAll_oversize','{V : Type} (w : List UInt8 → Run V IoError Nat) (fuel n : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.ok (n+1)⟩) (bad : ¬ n+1 ≤ (b::bs).length) : writeAll w (fuel+1) (b::bs)=⟨es,.panic⟩','by simp only [writeAll,h,if_neg bad]'),
('writeAll_progress','{V : Type} (w : List UInt8 → Run V IoError Nat) (fuel n : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.ok (n+1)⟩) (bound : n+1 ≤ (b::bs).length) : writeAll w (fuel+1) (b::bs)=pre es (writeAll w fuel ((b::bs).drop (n+1)))','by simp only [writeAll,h,if_pos bound]'),
]+[(f'writeAll_{x}',f'{{V : Type}} (w : List UInt8 → Run V IoError Nat) (fuel : Nat) (b : UInt8) (bs : List UInt8) (es : List V) (h : w (b::bs)=⟨es,.{x}⟩) : writeAll w (fuel+1) (b::bs)=⟨es,.{x}⟩','by simp only [writeAll,h]') for x in ['panic','oom','abort','diverge']])
module('Cleanup',['PV_DIAG11_Execution'],r'''
/-! Explicit cleanup on ordinary Rust Result return. Abnormal leaf traces
already include any unwind/abort cleanup; this function never invents it.
The drop primitive is a Run, so its effects, panic, OOM and divergence survive. -/
def dropReturned {V E A : Type} (r : Run V E A) (drop : Run V E Unit) : Run V E A :=
 match r.exit with
 | .ok a => pre r.events (seq drop (fun _ => ret a))
 | .error e => pre r.events (seq drop (fun _ => ⟨[],.error e⟩))
 | .panic => r | .oom => r | .abort => r | .diverge => r
''',[
('drop_ok','{V E A : Type} (es : List V) (a : A) (d : Run V E Unit) : dropReturned ⟨es,.ok a⟩ d=pre es (seq d (fun _ => ret a))','rfl'),
('drop_error','{V E A : Type} (es : List V) (e : E) (d : Run V E Unit) : dropReturned (⟨es,.error e⟩ : Run V E A) d=pre es (seq d (fun _ => ⟨[],.error e⟩))','rfl'),
('drop_normal_ok','{V E A : Type} (es ds : List V) (a : A) : dropReturned (⟨es,.ok a⟩ : Run V E A) ⟨ds,.ok ()⟩=⟨es++ds,.ok a⟩','by simp only [dropReturned,seq,ret,pre,List.append_nil]'),
('drop_normal_error','{V E A : Type} (es ds : List V) (e : E) : dropReturned (⟨es,.error e⟩ : Run V E A) ⟨ds,.ok ()⟩=⟨es++ds,.error e⟩','by simp only [dropReturned,seq,pre,List.append_nil]'),
('drop_panics_after_ok','{V E A : Type} (es ds : List V) (a : A) : dropReturned (⟨es,.ok a⟩ : Run V E A) ⟨ds,.panic⟩=⟨es++ds,.panic⟩','rfl'),
('drop_panics_after_error','{V E A : Type} (es ds : List V) (e : E) : dropReturned (⟨es,.error e⟩ : Run V E A) ⟨ds,.panic⟩=⟨es++ds,.panic⟩','rfl'),
]+[(f'drop_abnormal_{x}',f'{{V E A : Type}} (es : List V) (d : Run V E Unit) : dropReturned (⟨es,.{x}⟩ : Run V E A) d=⟨es,.{x}⟩','rfl') for x in ['panic','oom','abort','diverge']])
module('File',['PV_DIAG11_WriteAll','PV_DIAG11_Cleanup'],r'''
/-! std::fs::write::inner: File::create(path)?.write_all(contents),
then the returned File temporary is dropped on ordinary Ok/Err. Path/content
AsRef conversions and their evaluation precede this inner function. -/
def fileWrite {V F : Type} (create : Run V IoError F)
 (write : F → Run V IoError Unit) (close : F → Run V IoError Unit) : Run V IoError Unit :=
 seq create (fun f => dropReturned (write f) (close f))
''',[
('file_create_error','{V F : Type} (es : List V) (e : IoError) (w c : F → Run V IoError Unit) : fileWrite ⟨es,.error e⟩ w c=⟨es,.error e⟩','rfl'),
('file_created','{V F : Type} (es : List V) (f : F) (w c : F → Run V IoError Unit) : fileWrite ⟨es,.ok f⟩ w c=pre es (dropReturned (w f) (c f))','rfl'),
('file_success_order','{V F : Type} (es ws cs : List V) (f : F) : fileWrite (⟨es,.ok f⟩ : Run V IoError F) (fun _ => ⟨ws,.ok ()⟩) (fun _ => ⟨cs,.ok ()⟩)=⟨es++(ws++cs),.ok ()⟩','by simp only [fileWrite,seq,dropReturned,ret,pre,List.append_nil]'),
('file_write_error_closes','{V F : Type} (es ws cs : List V) (f : F) (e : IoError) : fileWrite (⟨es,.ok f⟩ : Run V IoError F) (fun _ => ⟨ws,.error e⟩) (fun _ => ⟨cs,.ok ()⟩)=⟨es++(ws++cs),.error e⟩','by simp only [fileWrite,seq,dropReturned,pre,List.append_nil]'),
]+[(f'file_create_{x}',f'{{V F : Type}} (es : List V) (w c : F → Run V IoError Unit) : fileWrite ⟨es,.{x}⟩ w c=⟨es,.{x}⟩','rfl') for x in ['panic','oom','abort','diverge']]+[
('file_write_panic_keeps_leaf_cleanup','{V F : Type} (es ws : List V) (f : F) (c : F → Run V IoError Unit) : fileWrite ⟨es,.ok f⟩ (fun _ => ⟨ws,.panic⟩) c=⟨es++ws,.panic⟩','rfl'),
('file_write_prefix','{V F : Type} (openFile : Run V IoError F) (w c : F → Run V IoError Unit) : ∃ xs, (fileWrite openFile w c).events=openFile.events++xs','seq_prefix openFile _'),
])
module('Print',['PV_DIAG11_Execution'],r'''
/-! stdio::print_to versus attempt_print_to_stderr. The capture helper's
complete effects and Boolean return are explicit. Capture failure falls back;
normal global write Err panics for print_to and is ignored for Termination.
Panic hooks, TLS, mutex poisoning and formatter effects belong to the primitives. -/
def printGlobal {V : Type} (w : Run V IoError Unit) : Run V IoError Unit :=
 ⟨w.events,match w.exit with | .error _ => .panic | x => x⟩
def ignoreIoError {V : Type} (w : Run V IoError Unit) : Run V IoError Unit :=
 ⟨w.events,match w.exit with | .error _ => .ok () | x => x⟩
def printTo {V : Type} (capture : Run V IoError Bool) (global : Run V IoError Unit) : Run V IoError Unit :=
 seq capture (fun used => if used then ret () else printGlobal global)
def attemptStderr {V : Type} (capture : Run V IoError Bool) (global : Run V IoError Unit) : Run V IoError Unit :=
 seq capture (fun used => if used then ret () else ignoreIoError global)
''',[
('print_capture_returns','{V : Type} (es : List V) (g : Run V IoError Unit) : printTo ⟨es,.ok true⟩ g=⟨es,.ok ()⟩','by simp only [printTo,seq,pre,ret,List.append_nil]; rfl'),
('print_fallback','{V : Type} (es : List V) (g : Run V IoError Unit) : printTo ⟨es,.ok false⟩ g=pre es (printGlobal g)','rfl'),
('print_global_error_panics','{V : Type} (es : List V) (e : IoError) : printGlobal (⟨es,.error e⟩ : Run V IoError Unit)=⟨es,.panic⟩','rfl'),
('stderr_global_error_ignored','{V : Type} (es : List V) (e : IoError) : ignoreIoError (⟨es,.error e⟩ : Run V IoError Unit)=⟨es,.ok ()⟩','rfl'),
('stderr_capture_returns','{V : Type} (es : List V) (g : Run V IoError Unit) : attemptStderr ⟨es,.ok true⟩ g=⟨es,.ok ()⟩','by simp only [attemptStderr,seq,pre,ret,List.append_nil]; rfl'),
('stderr_fallback','{V : Type} (es : List V) (g : Run V IoError Unit) : attemptStderr ⟨es,.ok false⟩ g=pre es (ignoreIoError g)','rfl'),
('stderr_partial_error_kept','{V : Type} (es ws : List V) (e : IoError) : attemptStderr (⟨es,.ok false⟩ : Run V IoError Bool) ⟨ws,.error e⟩=⟨es++ws,.ok ()⟩','rfl'),
('print_partial_error_kept','{V : Type} (es ws : List V) (e : IoError) : printTo (⟨es,.ok false⟩ : Run V IoError Bool) ⟨ws,.error e⟩=⟨es++ws,.panic⟩','rfl'),
]+[(f'stderr_formatter_{x}',f'{{V : Type}} (es : List V) : ignoreIoError (⟨es,.{x}⟩ : Run V IoError Unit)=⟨es,.{x}⟩','rfl') for x in ['panic','oom','abort','diverge']])
module('Report',['PV_DIAG11_Print'],r'''
/-! std::process::Termination for Result<T,E>. Debug formatting is not
assumed total, and reporting a returned Err is distinct from model panic.
Dropping err after the call is represented separately by the caller. -/
def report {V E A : Type} (result : Except E A) (okReport : A → Run V IoError Nat)
 (debugStderr : E → Run V IoError Unit) : Run V IoError Nat :=
 match result with
 | .ok a => okReport a
 | .error e => seq (debugStderr e) (fun _ => ret 1)
''',[
('report_ok','{V E A : Type} (a : A) (ok : A → Run V IoError Nat) (err : E → Run V IoError Unit) : report (.ok a) ok err=ok a','rfl'),
('report_err','{V E A : Type} (e : E) (ok : A → Run V IoError Nat) (err : E → Run V IoError Unit) : report (.error e) ok err=seq (err e) (fun _ => ret 1)','rfl'),
('report_success_silent','{V E : Type} (err : E → Run V IoError Unit) : report (.ok ()) (fun _ => (ret 0 : Run V IoError Nat)) err=ret 0','rfl'),
('report_error_failure_exit','{V E A : Type} (e : E) (es : List V) (ok : A → Run V IoError Nat) : report (.error e) ok (fun _ => ⟨es,.ok ()⟩)=⟨es,.ok 1⟩','by simp only [report,seq,ret,pre,List.append_nil]'),
]+[(f'report_debug_{x}',f'{{V E A : Type}} (e : E) (es : List V) (ok : A → Run V IoError Nat) : report (.error e) ok (fun _ => ⟨es,.{x}⟩)=⟨es,.{x}⟩','rfl') for x in ['panic','oom','abort','diverge']])
module('Client',['PV_DIAG11_File','PV_DIAG11_Report'],r'''
/-! The deployed plan::prove tail and main action branch. Every argument is
an entire reached call trace, not just its successful bytes. The tail starts
at the two fs::write statements; JSON may itself fail, panic or allocate.
Earlier recovery/nonce/prover traces precede this tail and are retained by seq. -/
def clientTail {V J : Type} (proof statement : Run V IoError Unit)
 (json : Run V IoError J) : Run V IoError J := seq proof (fun _ => seq statement (fun _ => json))
def actionMain {V J : Type} (plan : Run V IoError J) (print : J → Run V IoError Unit) : Run V IoError Unit :=
 seq plan (fun j => seq (print j) (fun _ => ret ()))
''',[
('client_proof_error_stops','{V J : Type} (es : List V) (e : IoError) (s : Run V IoError Unit) (j : Run V IoError J) : clientTail ⟨es,.error e⟩ s j=⟨es,.error e⟩','rfl'),
('client_statement_error_stops','{V J : Type} (es ss : List V) (e : IoError) (j : Run V IoError J) : clientTail (⟨es,.ok ()⟩ : Run V IoError Unit) ⟨ss,.error e⟩ j=⟨es++ss,.error e⟩','rfl'),
('client_json_after_writes','{V J : Type} (es ss : List V) (j : Run V IoError J) : clientTail (⟨es,.ok ()⟩ : Run V IoError Unit) ⟨ss,.ok ()⟩ j=pre (es++ss) j','by exact pre_assoc es ss j'),
('main_plan_error_no_print','{V J : Type} (es : List V) (e : IoError) (p : J → Run V IoError Unit) : actionMain ⟨es,.error e⟩ p=⟨es,.error e⟩','rfl'),
('main_print_error_keeps_prefix','{V J : Type} (es ps : List V) (j : J) (e : IoError) : actionMain (⟨es,.ok j⟩ : Run V IoError J) (fun _ => ⟨ps,.error e⟩)=⟨es++ps,.error e⟩','rfl'),
('main_success_order','{V J : Type} (es ps : List V) (j : J) : actionMain (⟨es,.ok j⟩ : Run V IoError J) (fun _ => ⟨ps,.ok ()⟩)=⟨es++ps,.ok ()⟩','by simp only [actionMain,seq,ret,pre,List.append_nil]'),
]+[(f'client_proof_{x}',f'{{V J : Type}} (es : List V) (s : Run V IoError Unit) (j : Run V IoError J) : clientTail ⟨es,.{x}⟩ s j=⟨es,.{x}⟩','rfl') for x in ['panic','oom','abort','diverge']]+[
('client_tail_prefix','{V J : Type} (p s : Run V IoError Unit) (j : Run V IoError J) : ∃ xs, (clientTail p s j).events=p.events++xs','seq_prefix p _'),
('main_plan_prefix','{V J : Type} (p : Run V IoError J) (f : J → Run V IoError Unit) : ∃ xs, (actionMain p f).events=p.events++xs','seq_prefix p _'),
])
(D/'plans.json').write_text(json.dumps(plans,indent=2)+'\n')
print({k:len(v) for k,v in plans.items()},'total',sum(map(len,plans.values())))
# Printing panics have their own effects; io::Error and returned errors have
# destructors. They are not erased by changing an exit constructor.
module('Print',['PV_DIAG11_Cleanup','PV_DIAG11_WriteAll'],r'''
/-! Source control for print_to and attempt_print_to_stderr, retaining capture,
formatter, panic hook AND io::Error destruction as separate complete runs. -/
def printGlobal {V : Type} (w : Run V IoError Unit)
 (panic : IoError → Run V IoError Unit) : Run V IoError Unit :=
 match w.exit with | .error e => pre w.events (panic e) | _ => w
def ignoreIoError {V : Type} (w : Run V IoError Unit)
 (dropError : IoError → Run V IoError Unit) : Run V IoError Unit :=
 match w.exit with | .error e => pre w.events (dropError e) | _ => w
def printTo {V : Type} (capture : Run V IoError Bool) (global : Run V IoError Unit)
 (panic : IoError → Run V IoError Unit) : Run V IoError Unit :=
 seq capture (fun used => if used then ret () else printGlobal global panic)
def attemptStderr {V : Type} (capture : Run V IoError Bool) (global : Run V IoError Unit)
 (dropError : IoError → Run V IoError Unit) : Run V IoError Unit :=
 seq capture (fun used => if used then ret () else ignoreIoError global dropError)
''',[
('print_capture_returns','{V : Type} (es : List V) (g : Run V IoError Unit) (p : IoError → Run V IoError Unit) : printTo ⟨es,.ok true⟩ g p=⟨es,.ok ()⟩','by simp only [printTo,seq,pre,ret,List.append_nil]; rfl'),
('print_fallback','{V : Type} (es : List V) (g : Run V IoError Unit) (p : IoError → Run V IoError Unit) : printTo ⟨es,.ok false⟩ g p=pre es (printGlobal g p)','rfl'),
('print_error_invokes_hook','{V : Type} (es : List V) (e : IoError) (p : IoError → Run V IoError Unit) : printGlobal ⟨es,.error e⟩ p=pre es (p e)','rfl'),
('stderr_error_dropped','{V : Type} (es : List V) (e : IoError) (d : IoError → Run V IoError Unit) : ignoreIoError ⟨es,.error e⟩ d=pre es (d e)','rfl'),
('stderr_capture_returns','{V : Type} (es : List V) (g : Run V IoError Unit) (d : IoError → Run V IoError Unit) : attemptStderr ⟨es,.ok true⟩ g d=⟨es,.ok ()⟩','by simp only [attemptStderr,seq,pre,ret,List.append_nil]; rfl'),
('stderr_fallback','{V : Type} (es : List V) (g : Run V IoError Unit) (d : IoError → Run V IoError Unit) : attemptStderr ⟨es,.ok false⟩ g d=pre es (ignoreIoError g d)','rfl'),
('stderr_partial_error_prefix','{V : Type} (es ws ds : List V) (e : IoError) : attemptStderr (⟨es,.ok false⟩ : Run V IoError Bool) ⟨ws,.error e⟩ (fun _ => ⟨ds,.ok ()⟩)=⟨es++(ws++ds),.ok ()⟩','rfl'),
('print_partial_error_hook_prefix','{V : Type} (es ws hs : List V) (e : IoError) : printTo (⟨es,.ok false⟩ : Run V IoError Bool) ⟨ws,.error e⟩ (fun _ => ⟨hs,.panic⟩)=⟨es++(ws++hs),.panic⟩','rfl'),
]+[(f'stderr_formatter_{x}',f'{{V : Type}} (es : List V) (d : IoError → Run V IoError Unit) : ignoreIoError ⟨es,.{x}⟩ d=⟨es,.{x}⟩','rfl') for x in ['panic','oom','abort','diverge']])
module('Report',['PV_DIAG11_Print'],r'''
/-! Termination<Result<T,E>> with complete debugStderr and E drop runs.
Native drop/unwind implementations remain explicit primitives. -/
def report {V E A : Type} (result : Except E A) (okReport : A → Run V IoError Nat)
 (debugStderr dropError : E → Run V IoError Unit) : Run V IoError Nat :=
 match result with
 | .ok a => okReport a
 | .error e => dropReturned (seq (debugStderr e) (fun _ => ret 1)) (dropError e)
''',[
('report_ok','{V E A : Type} (a : A) (ok : A → Run V IoError Nat) (err d : E → Run V IoError Unit) : report (.ok a) ok err d=ok a','rfl'),
('report_err','{V E A : Type} (e : E) (ok : A → Run V IoError Nat) (err d : E → Run V IoError Unit) : report (.error e) ok err d=dropReturned (seq (err e) (fun _ => ret 1)) (d e)','rfl'),
('report_success_silent','{V E : Type} (err d : E → Run V IoError Unit) : report (.ok ()) (fun _ => (ret 0 : Run V IoError Nat)) err d=ret 0','rfl'),
('report_error_failure_exit','{V E A : Type} (e : E) (es ds : List V) (ok : A → Run V IoError Nat) : report (.error e) ok (fun _ => ⟨es,.ok ()⟩) (fun _ => ⟨ds,.ok ()⟩)=⟨es++ds,.ok 1⟩','by simp only [report,seq,ret,pre,dropReturned,List.append_nil]'),
]+[(f'report_debug_{x}',f'{{V E A : Type}} (e : E) (es : List V) (ok : A → Run V IoError Nat) (d : E → Run V IoError Unit) : report (.error e) ok (fun _ => ⟨es,.{x}⟩) d=⟨es,.{x}⟩','rfl') for x in ['panic','oom','abort','diverge']])
(D/'plans.json').write_text(json.dumps(plans,indent=2)+'\n')
