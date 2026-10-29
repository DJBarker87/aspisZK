"""Incremental focused declarations. Each compile adds a used semantic case;
no repeated unchanged regression. --check validates final sources."""
from pathlib import Path
import json,sys
E=Path(__file__).parent
plans={}
def plan(name,imports,base,steps):
 plans['PV_DIAG3_'+name]=dict(imports=imports,base=base,steps=steps)
def th(s):
 import re
 name=re.search(r'theorem\s+(\w+)',s)[1]
 return s+'\n#print axioms '+name
plan('Execution',['Init'],'''/-! Diagnostic execution carrier. These are specifications, not native
instances. Unlike diag2, abort and divergent prependes do not run unwind glue.
No effects or final state are erased by an abnormal terminal. -/
set_option autoImplicit false
namespace PV_DIAG3
abbrev Bytes := List UInt8
structure Panic where
 message : Bytes
 frames : List Nat
 thread : Bytes
 location : Bytes
 deriving DecidableEq, Repr
structure Crash where
 reason : Bytes
 registers : Bytes
 memory : Bytes
 frames : List Nat
 deriving DecidableEq, Repr
inductive Event where
 | requested (fd : Nat) (bytes : Bytes)
 | delivered (fd : Nat) (bytes : Bytes)
 | returned (bytes : Bytes)
 | capture (frames : List Nat)
 | panic (value : Panic)
 | crash (value : Crash)
 | allocation (size align : Nat)
 | foreign (bytes : Bytes) (frames : List Nat)
 deriving DecidableEq, Repr
inductive Exit (A : Type) where
 | value (a : A)
 | panic (p : Panic)
 | abort (c : Crash)
 | diverge
 deriving Repr
structure Execution (S A : Type) where
 events : List Event
 state : S
 exit : Exit A
 deriving Repr
abbrev Op (S A : Type) := S → Execution S A
variable {S A B C : Type}
def pure (a : A) : Op S A := fun s => ⟨[],s,.value a⟩
def prepend (es : List Event) (x : Execution S A) : Execution S A :=
 ⟨es ++ x.events,x.state,x.exit⟩
def bind (x : Execution S A) (f : A → Op S B) : Execution S B :=
 match x.exit with
 | .value a => prepend x.events (f a x.state)
 | .panic p => ⟨x.events,x.state,.panic p⟩
 | .abort c => ⟨x.events,x.state,.abort c⟩
 | .diverge => ⟨x.events,x.state,.diverge⟩
def sequence (x : Op S A) (f : A → Op S B) : Op S B := fun s => bind (x s) f
''',[
th('''theorem prepend_nil (x : Execution S A) : prepend [] x = x := by cases x; rfl'''),
th('''theorem prepend_append (a b : List Event) (x : Execution S A) :
 prepend (a++b) x = prepend a (prepend b x) := by
 cases x; simp [prepend,List.append_assoc]'''),
th('''theorem bind_value (es : List Event) (s : S) (a : A) (f : A → Op S B) :
 bind ⟨es,s,.value a⟩ f = prepend es (f a s) := rfl'''),
th('''theorem bind_panic (es : List Event) (s : S) (p : Panic) (f : A → Op S B) :
 bind ⟨es,s,.panic p⟩ f = ⟨es,s,.panic p⟩ := rfl'''),
th('''theorem bind_abort (es : List Event) (s : S) (c : Crash) (f : A → Op S B) :
 bind ⟨es,s,.abort c⟩ f = ⟨es,s,.abort c⟩ := rfl'''),
th('''theorem bind_diverge (es : List Event) (s : S) (f : A → Op S B) :
 bind ⟨es,s,.diverge⟩ f = ⟨es,s,.diverge⟩ := rfl'''),
th('''theorem pure_bind (a : A) (s : S) (f : A → Op S B) :
 bind (pure a s) f = f a s := by simp [bind,pure,prepend]'''),
th('''theorem bind_pure (x : Execution S A) : bind x pure = x := by
 cases x with | mk es s ex => cases ex <;> simp [bind,pure,prepend]'''),
th('''theorem bind_prepend (es : List Event) (x : Execution S A) (f : A → Op S B) :
 bind (prepend es x) f = prepend es (bind x f) := by
 cases x with | mk xs s ex => cases ex <;> simp [bind,prepend,List.append_assoc]'''),
th('''theorem bind_assoc (x : Execution S A) (f : A → Op S B) (g : B → Op S C) :
 bind (bind x f) g = bind x (fun a s => bind (f a s) g) := by
 cases x with
 | mk es s ex =>
   cases ex with
   | value a => exact bind_prepend es (f a s) g
   | panic p => rfl
   | abort c => rfl
   | diverge => rfl'''),
th('''theorem bind_state_after_normal (es : List Event) (s : S) (a : A)
 (f : A → Op S B) : (bind ⟨es,s,.value a⟩ f).state = (f a s).state := rfl'''),
th('''theorem bind_events_after_normal (es : List Event) (s : S) (a : A)
 (f : A → Op S B) : (bind ⟨es,s,.value a⟩ f).events = es ++ (f a s).events := rfl''')])

plan('Ownership',['PV_DIAG3_Execution'],'''/-! Rust lexical cleanup. The actual destructor and double-panic runtime
executions remain explicit; no destructor-silence assumption is introduced. -/
set_option autoImplicit false
namespace PV_DIAG3
variable {S A : Type}
def unwind (p : Panic) (drop : Op S Unit)
 (doublePanic : Panic → Panic → Op S A) : Op S A := fun s =>
 let d := drop s
 prepend d.events (match d.exit with
 | .value () => ⟨[],d.state,.panic p⟩
 | .panic q => doublePanic p q d.state
 | .abort c => ⟨[],d.state,.abort c⟩
 | .diverge => ⟨[],d.state,.diverge⟩)
def scope (body : Op S A) (drop : Op S Unit)
 (doublePanic : Panic → Panic → Op S A) : Op S A := fun s =>
 let b := body s
 prepend b.events (match b.exit with
 | .value a => bind (drop b.state) (fun _ => pure a)
 | .panic p => unwind p drop doublePanic b.state
 | .abort c => ⟨[],b.state,.abort c⟩
 | .diverge => ⟨[],b.state,.diverge⟩)
''',[
th('''theorem scope_value (es : List Event) (s t : S) (a : A)
 (body : Op S A) (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (h : body s = ⟨es,t,.value a⟩) :
 scope body drop dp s = prepend es (bind (drop t) (fun _ => pure a)) := by
 simp only [scope,h]'''),
th('''theorem scope_panic (es : List Event) (s t : S) (p : Panic)
 (body : Op S A) (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (h : body s = ⟨es,t,.panic p⟩) :
 scope body drop dp s = prepend es (unwind p drop dp t) := by simp only [scope,h]'''),
th('''theorem scope_abort_no_cleanup (es : List Event) (s t : S) (c : Crash)
 (body : Op S A) (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (h : body s = ⟨es,t,.abort c⟩) :
 scope body drop dp s = ⟨es,t,.abort c⟩ := by simp [scope,h,prepend]'''),
th('''theorem scope_diverge_no_cleanup (es : List Event) (s t : S)
 (body : Op S A) (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (h : body s = ⟨es,t,.diverge⟩) :
 scope body drop dp s = ⟨es,t,.diverge⟩ := by simp [scope,h,prepend]'''),
th('''theorem unwind_returns_original_panic (es : List Event) (s t : S) (p : Panic)
 (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (h : drop s = ⟨es,t,.value ()⟩) :
 unwind p drop dp s = ⟨es,t,.panic p⟩ := by simp [unwind,h,prepend]'''),
th('''theorem unwind_double_panic (es : List Event) (s t : S) (p q : Panic)
 (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (h : drop s = ⟨es,t,.panic q⟩) :
 unwind p drop dp s = prepend es (dp p q t) := by simp only [unwind,h]'''),
th('''theorem unwind_abort_keeps_crash (es : List Event) (s t : S) (p : Panic) (c : Crash)
 (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (h : drop s = ⟨es,t,.abort c⟩) :
 unwind p drop dp s = ⟨es,t,.abort c⟩ := by simp [unwind,h,prepend]'''),
th('''theorem unwind_divergent_prefix (es : List Event) (s t : S) (p : Panic)
 (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (h : drop s = ⟨es,t,.diverge⟩) :
 unwind p drop dp s = ⟨es,t,.diverge⟩ := by simp [unwind,h,prepend]'''),
th('''theorem normal_drop_order (a : A) (s t u : S) (bs ds : List Event)
 (body : Op S A) (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (hb : body s = ⟨bs,t,.value a⟩) (hd : drop t = ⟨ds,u,.value ()⟩) :
 scope body drop dp s = ⟨bs++ds,u,.value a⟩ := by
 simp [scope,hb,hd,bind,prepend,pure]'''),
th('''theorem normal_drop_panics (a : A) (s t u : S) (bs ds : List Event) (p : Panic)
 (body : Op S A) (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (hb : body s = ⟨bs,t,.value a⟩) (hd : drop t = ⟨ds,u,.panic p⟩) :
 scope body drop dp s = ⟨bs++ds,u,.panic p⟩ := by
 simp [scope,hb,hd,bind,prepend]'''),
th('''theorem normal_drop_aborts (a : A) (s t u : S) (bs ds : List Event) (c : Crash)
 (body : Op S A) (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (hb : body s = ⟨bs,t,.value a⟩) (hd : drop t = ⟨ds,u,.abort c⟩) :
 scope body drop dp s = ⟨bs++ds,u,.abort c⟩ := by
 simp [scope,hb,hd,bind,prepend]'''),
th('''theorem normal_drop_diverges (a : A) (s t u : S) (bs ds : List Event)
 (body : Op S A) (drop : Op S Unit) (dp : Panic → Panic → Op S A)
 (hb : body s = ⟨bs,t,.value a⟩) (hd : drop t = ⟨ds,u,.diverge⟩) :
 scope body drop dp s = ⟨bs++ds,u,.diverge⟩ := by
 simp [scope,hb,hd,bind,prepend]''')])

plan('Write',['PV_DIAG3_Ownership'],'''/-! std::io::Write::write_all, including interrupted-error destruction,
partial writes and the checked slice failure. The leaf guard includes its
abnormal owned-error cleanup; its law is a separate native obligation. -/
set_option autoImplicit false
namespace PV_DIAG3
variable {S E : Type}
structure WriteOps (S E : Type) where
 write : Bytes → Op S (Except E Nat)
 zeroError : E
 interruptedGuard : E → Op S Bool
 dropInterrupted : E → Op S Unit
 slicePanic : Bytes → Nat → Op S (Except E Unit)
def writeAllStep (o : WriteOps S E) (buf : Bytes)
 (next : Bytes → Op S (Except E Unit)) : Op S (Except E Unit) :=
 if buf.isEmpty then pure (.ok ()) else
 sequence (o.write buf) (fun r => match r with
 | .ok 0 => pure (.error o.zeroError)
 | .ok (n+1) => if n+1 ≤ buf.length then next (buf.drop (n+1)) else o.slicePanic buf (n+1)
 | .error e => sequence (o.interruptedGuard e) (fun interrupted =>
   if interrupted then sequence (o.dropInterrupted e) (fun _ => next buf)
   else pure (.error e)))
/-- The suffix is supplied, not replaced by an arbitrary fuel exhaustion.
Every native finite prefix can be interpreted without asserting termination. -/
def writePrefix (o : WriteOps S E) : Nat → (Bytes → Op S (Except E Unit)) →
 Bytes → Op S (Except E Unit)
 | 0,suffix => suffix
 | n+1,suffix => fun buf => writeAllStep o buf (writePrefix o n suffix)
''',[
th('''theorem write_empty (o : WriteOps S E) (k : Bytes → Op S (Except E Unit)) :
 writeAllStep o [] k = pure (.ok ()) := rfl'''),
th('''theorem write_zero (o : WriteOps S E) (buf : Bytes) (s t : S) (es : List Event)
 (k : Bytes → Op S (Except E Unit)) (hne : buf.isEmpty = false)
 (h : o.write buf s = ⟨es,t,.value (.ok 0)⟩) :
 writeAllStep o buf k s = ⟨es,t,.value (.error o.zeroError)⟩ := by
 simp [writeAllStep,hne,sequence,h,bind,prepend,pure]'''),
th('''theorem write_partial (o : WriteOps S E) (buf : Bytes) (s t : S) (es : List Event)
 (k : Bytes → Op S (Except E Unit)) (n : Nat) (hne : buf.isEmpty = false)
 (hn : n+1 ≤ buf.length) (h : o.write buf s = ⟨es,t,.value (.ok (n+1))⟩) :
 writeAllStep o buf k s = prepend es (k (buf.drop (n+1)) t) := by
 simp [writeAllStep,hne,sequence,h,bind,hn]'''),
th('''theorem write_bad_count (o : WriteOps S E) (buf : Bytes) (s t : S) (es : List Event)
 (k : Bytes → Op S (Except E Unit)) (n : Nat) (hne : buf.isEmpty = false)
 (hn : ¬ n+1 ≤ buf.length) (h : o.write buf s = ⟨es,t,.value (.ok (n+1))⟩) :
 writeAllStep o buf k s = prepend es (o.slicePanic buf (n+1) t) := by
 simp [writeAllStep,hne,sequence,h,bind,hn]'''),
th('''theorem write_interrupted_drop (o : WriteOps S E) (buf : Bytes) (s t u : S)
 (es gs : List Event) (e : E) (k : Bytes → Op S (Except E Unit))
 (hne : buf.isEmpty = false) (hw : o.write buf s = ⟨es,t,.value (.error e)⟩)
 (hg : o.interruptedGuard e t = ⟨gs,u,.value true⟩) :
 writeAllStep o buf k s = prepend (es++gs)
 (bind (o.dropInterrupted e u) (fun _ => k buf)) := by
 simp [writeAllStep,hne,sequence,hw,hg,bind,prepend,List.append_assoc]'''),
th('''theorem write_error_return (o : WriteOps S E) (buf : Bytes) (s t u : S)
 (es gs : List Event) (e : E) (k : Bytes → Op S (Except E Unit))
 (hne : buf.isEmpty = false) (hw : o.write buf s = ⟨es,t,.value (.error e)⟩)
 (hg : o.interruptedGuard e t = ⟨gs,u,.value false⟩) :
 writeAllStep o buf k s = ⟨es++gs,u,.value (.error e)⟩ := by
 simp [writeAllStep,hne,sequence,hw,hg,bind,prepend,pure]'''),
th('''theorem write_prefix_zero (o : WriteOps S E) (suffix : Bytes → Op S (Except E Unit)) :
 writePrefix o 0 suffix = suffix := rfl'''),
th('''theorem write_prefix_successor (o : WriteOps S E) (n : Nat)
 (suffix : Bytes → Op S (Except E Unit)) (buf : Bytes) :
 writePrefix o (n+1) suffix buf = writeAllStep o buf (writePrefix o n suffix) := rfl''')])

plan('Capture',['PV_DIAG3_Ownership'],'''/-! Deployed Backtrace::create callback and lazy ownership. Frames are
native observations, not invented source labels. Foreign trace/resolve and
lock effects remain explicit operations on the same state. -/
set_option autoImplicit false
namespace PV_DIAG3
structure Frame where
 pc : Nat
 symbolAddress : Nat
 deriving DecidableEq, Repr
structure CaptureState where
 frames : List Frame
 actualStart : Option Nat
 deriving DecidableEq, Repr
inductive TraceValue where
 | unsupported
 | disabled
 | captured (frames : List Frame) (start : Nat)
 deriving DecidableEq, Repr
def pushFrame (ip : Nat) (c : CaptureState) (f : Frame) : CaptureState :=
 let frames := c.frames ++ [f]
 ⟨frames,if f.symbolAddress == ip && c.actualStart.isNone then some frames.length else c.actualStart⟩
def finishCapture (c : CaptureState) : TraceValue :=
 if c.frames.isEmpty then .unsupported else .captured c.frames (c.actualStart.getD 0)
def traceStatus : TraceValue → Nat
 | .unsupported => 0
 | .disabled => 1
 | .captured _ _ => 2
variable {S : Type}
structure CaptureOps (S : Type) where
 lock : Op S Unit
 unlock : Op S Unit
 imageBase : Op S Unit
 trace : CaptureState → Op S CaptureState
 package : TraceValue → Op S TraceValue
 doublePanic : Panic → Panic → Op S TraceValue
/-- package includes LazyLock capture ownership and its failure cleanup.
trace includes frame clone/push, callbacks, PC selection and their cleanup. -/
def createTrace (o : CaptureOps S) : Op S TraceValue :=
 sequence o.lock (fun _ => scope
  (sequence o.imageBase (fun _ => sequence (o.trace ⟨[],none⟩)
    (fun c => o.package (finishCapture c)))) o.unlock o.doublePanic)
''',[
th('''theorem push_frame_preserves_order (ip : Nat) (c : CaptureState) (f : Frame) :
 (pushFrame ip c f).frames = c.frames ++ [f] := rfl'''),
th('''theorem first_symbol_match (ip : Nat) (fs : List Frame) (f : Frame)
 (h : f.symbolAddress = ip) :
 (pushFrame ip ⟨fs,none⟩ f).actualStart = some (fs++[f]).length := by
 simp [pushFrame,h]'''),
th('''theorem later_symbol_match_keeps_first (ip k : Nat) (fs : List Frame) (f : Frame) :
 (pushFrame ip ⟨fs,some k⟩ f).actualStart = some k := by simp [pushFrame]'''),
th('''theorem nonmatch_keeps_search (ip : Nat) (fs : List Frame) (f : Frame)
 (h : f.symbolAddress ≠ ip) :
 (pushFrame ip ⟨fs,none⟩ f).actualStart = none := by simp [pushFrame,h]'''),
th('''theorem empty_trace_unsupported (start : Option Nat) :
 finishCapture ⟨[],start⟩ = .unsupported := rfl'''),
th('''theorem missing_ip_starts_zero (f : Frame) (fs : List Frame) :
 finishCapture ⟨f::fs,none⟩ = .captured (f::fs) 0 := rfl'''),
th('''theorem captured_start_exact (f : Frame) (fs : List Frame) (k : Nat) :
 finishCapture ⟨f::fs,some k⟩ = .captured (f::fs) k := rfl'''),
th('''theorem trace_status_no_symbolization (frames : List Frame) (start : Nat) :
 traceStatus (.captured frames start) = 2 := rfl'''),
th('''theorem create_lock_aborts (o : CaptureOps S) (s t : S)
 (es : List Event) (c : Crash) (h : o.lock s = ⟨es,t,.abort c⟩) :
 createTrace o s = ⟨es,t,.abort c⟩ := by simp [createTrace,sequence,h,bind]'''),
th('''theorem create_lock_normal (o : CaptureOps S) (s t : S)
 (es : List Event) (h : o.lock s = ⟨es,t,.value ()⟩) :
 createTrace o s = prepend es
 (scope (sequence o.imageBase (fun _ => sequence (o.trace ⟨[],none⟩)
   (fun c => o.package (finishCapture c)))) o.unlock o.doublePanic t) := by
 simp only [createTrace,sequence,h,bind]''')])

plan('Formatter',['PV_DIAG3_Write'],'''/-! std::io::{Write::write_fmt,default_write_fmt}. The formatter leaf
retains its mutable Adapter.error and all abnormal cleanup. Ok formatter
return still drops the stored error; Err with no I/O error panics. -/
set_option autoImplicit false
namespace PV_DIAG3
variable {S E : Type}
structure FmtOps (S E : Type) where
 format : Op S (Except Unit Unit × Except E Unit)
 dropSlot : Except E Unit → Op S Unit
 impossibleFmt : Op S (Except E Unit)
def defaultFmt (o : FmtOps S E) : Op S (Except E Unit) :=
 sequence o.format (fun pair => match pair.1 with
 | .ok () => sequence (o.dropSlot pair.2) (fun _ => pure (.ok ()))
 | .error () => match pair.2 with
   | .error e => pure (.error e)
   | .ok () => o.impossibleFmt)
def writeFmt (known : Option Bytes) (writeAll : Bytes → Op S (Except E Unit))
 (o : FmtOps S E) : Op S (Except E Unit) :=
 match known with | some bytes => writeAll bytes | none => defaultFmt o
/-- Error-slot assignment includes destruction of the old slot and storage
of the new error, with ownership cleanup if replacement panics. -/
def adapterWrite (writeAll : Bytes → Op S (Except E Unit))
 (replaceError : E → Op S Unit) (bytes : Bytes) : Op S (Except Unit Unit) :=
 sequence (writeAll bytes) (fun r => match r with
 | .ok () => pure (.ok ())
 | .error e => sequence (replaceError e) (fun _ => pure (.error ())))
''',[
th('''theorem known_format_fast_path (bytes : Bytes) (w : Bytes → Op S (Except E Unit))
 (o : FmtOps S E) : writeFmt (some bytes) w o = w bytes := rfl'''),
th('''theorem dynamic_format_path (w : Bytes → Op S (Except E Unit)) (o : FmtOps S E) :
 writeFmt none w o = defaultFmt o := rfl'''),
th('''theorem formatter_success_drops_slot (o : FmtOps S E) (s t : S) (es : List Event)
 (slot : Except E Unit) (h : o.format s = ⟨es,t,.value (.ok (),slot)⟩) :
 defaultFmt o s = prepend es (bind (o.dropSlot slot t) (fun _ => pure (.ok ()))) := by
 simp only [defaultFmt,sequence,h,bind]'''),
th('''theorem formatter_io_error_moves_slot (o : FmtOps S E) (s t : S) (es : List Event)
 (e : E) (h : o.format s = ⟨es,t,.value (.error (),.error e)⟩) :
 defaultFmt o s = ⟨es,t,.value (.error e)⟩ := by
 simp [defaultFmt,sequence,h,bind,prepend,pure]'''),
th('''theorem formatter_spurious_error_panics (o : FmtOps S E) (s t : S) (es : List Event)
 (h : o.format s = ⟨es,t,.value (.error (),.ok ())⟩) :
 defaultFmt o s = prepend es (o.impossibleFmt t) := by simp only [defaultFmt,sequence,h,bind]'''),
th('''theorem adapter_success (w : Bytes → Op S (Except E Unit)) (store : E → Op S Unit)
 (bytes : Bytes) (s t : S) (es : List Event)
 (h : w bytes s = ⟨es,t,.value (.ok ())⟩) :
 adapterWrite w store bytes s = ⟨es,t,.value (.ok ())⟩ := by
 simp [adapterWrite,sequence,h,bind,prepend,pure]'''),
th('''theorem adapter_error_stores_first (w : Bytes → Op S (Except E Unit))
 (store : E → Op S Unit) (bytes : Bytes) (s t : S) (es : List Event) (e : E)
 (h : w bytes s = ⟨es,t,.value (.error e)⟩) :
 adapterWrite w store bytes s = prepend es (bind (store e t) (fun _ => pure (.error ()))) := by
 simp only [adapterWrite,sequence,h,bind]'''),
th('''theorem formatter_abort_no_slot_cleanup (o : FmtOps S E) (s t : S)
 (es : List Event) (c : Crash) (h : o.format s = ⟨es,t,.abort c⟩) :
 defaultFmt o s = ⟨es,t,.abort c⟩ := by simp [defaultFmt,sequence,h,bind]''')])

plan('Drop',['PV_DIAG3_Ownership'],'''/-! anyhow ErrorImpl field order, Box/Vec cleanup, and LazyLock::drop.
All allocator operations remain explicit. No deallocation is silently
classified as an empty effect or as publicly scheduled. -/
set_option autoImplicit false
namespace PV_DIAG3
variable {S : Type}
inductive LazyState where | incomplete | complete | poisoned
 deriving DecidableEq, Repr
def lazyDrop (state : LazyState) (dropClosure dropValue : Op S Unit) : Op S Unit :=
 match state with
 | .incomplete => dropClosure
 | .complete => dropValue
 | .poisoned => pure ()
def boxDeallocate (size : Nat) (deallocate : Op S Unit) : Op S Unit :=
 if size = 0 then pure () else deallocate
/-- The pointee is dropped before Box::drop; its allocation is also freed
when the pointee unwinds. RawVec similarly follows vector element cleanup. -/
def allocationDrop (payload deallocate : Op S Unit)
 (doublePanic : Panic → Panic → Op S Unit) : Op S Unit := scope payload deallocate doublePanic
/-- ErrorImpl<E>: static vtable reference, backtrace, then _object. The Box
allocation is released after fields; concrete payload Drop is not omitted. -/
def errorObjectDrop (backtrace message deallocate : Op S Unit)
 (doublePanic : Panic → Panic → Op S Unit) : Op S Unit :=
 allocationDrop (scope backtrace message doublePanic) deallocate doublePanic
''',[
th('''theorem lazy_incomplete_drops_closure (f v : Op S Unit) :
 lazyDrop .incomplete f v = f := rfl'''),
th('''theorem lazy_complete_drops_value (f v : Op S Unit) :
 lazyDrop .complete f v = v := rfl'''),
th('''theorem lazy_poisoned_no_field (f v : Op S Unit) :
 lazyDrop .poisoned f v = pure () := rfl'''),
th('''theorem box_zero_layout (free : Op S Unit) : boxDeallocate 0 free = pure () := by
 simp [boxDeallocate]'''),
th('''theorem box_nonzero_layout (n : Nat) (free : Op S Unit) :
 boxDeallocate (n+1) free = free := by simp [boxDeallocate]'''),
th('''theorem allocation_drop_aborts (payload free : Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t : S) (es : List Event) (c : Crash)
 (h : payload s = ⟨es,t,.abort c⟩) :
 allocationDrop payload free dp s = ⟨es,t,.abort c⟩ :=
 scope_abort_no_cleanup es s t c payload free dp h'''),
th('''theorem allocation_drop_panic_frees (payload free : Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t : S) (es : List Event) (p : Panic)
 (h : payload s = ⟨es,t,.panic p⟩) :
 allocationDrop payload free dp s = prepend es (unwind p free dp t) :=
 scope_panic es s t p payload free dp h'''),
th('''theorem error_fields_normal_order (b m free : Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t u v : S) (bs ms fs : List Event)
 (hb : b s = ⟨bs,t,.value ()⟩) (hm : m t = ⟨ms,u,.value ()⟩)
 (hf : free u = ⟨fs,v,.value ()⟩) :
 errorObjectDrop b m free dp s = ⟨bs++ms++fs,v,.value ()⟩ := by
 unfold errorObjectDrop allocationDrop
 have fields := normal_drop_order () s t u bs ms b m dp hb hm
 exact normal_drop_order () s u v (bs++ms) fs (scope b m dp) free dp fields hf''')])

plan('Reporting',['PV_DIAG3_Drop','PV_DIAG3_Formatter'],'''/-! Result::Termination and attempt_print_to_stderr with owned Error.
Native print/capture leaves retain their own buffer/lock/Result cleanup.
Error destruction follows reporting, including ignored I/O errors. -/
set_option autoImplicit false
namespace PV_DIAG3
variable {S E : Type}
def attemptStderr (capture : Op S Bool) (writeAndDrop : Op S Unit) : Op S Unit :=
 sequence capture (fun captured => if captured then pure () else writeAndDrop)
def reportOwned (result : Except E Unit) (report dropError : E → Op S Unit)
 (doublePanic : Panic → Panic → Op S Unit) : Op S Nat :=
 match result with
 | .ok () => pure 0
 | .error e => sequence (scope (report e) (dropError e) doublePanic) (fun _ => pure 1)
def ignoredWrite {I : Type} (write : Op S (Except I Unit))
 (dropResult : Except I Unit → Op S Unit) : Op S Unit := sequence write dropResult
''',[
th('''theorem reporting_success (r d : E → Op S Unit) (dp : Panic → Panic → Op S Unit) :
 reportOwned (.ok ()) r d dp = pure 0 := rfl'''),
th('''theorem captured_stderr_no_global (cap : Op S Bool) (w : Op S Unit)
 (s t : S) (es : List Event) (h : cap s = ⟨es,t,.value true⟩) :
 attemptStderr cap w s = ⟨es,t,.value ()⟩ := by
 simp [attemptStderr,sequence,h,bind,prepend,pure]'''),
th('''theorem uncaptured_stderr_keeps_write (cap : Op S Bool) (w : Op S Unit)
 (s t : S) (es : List Event) (h : cap s = ⟨es,t,.value false⟩) :
 attemptStderr cap w s = prepend es (w t) := by
 simp [attemptStderr,sequence,h,bind]'''),
th('''theorem ignored_write_error_cleanup {I : Type} (write : Op S (Except I Unit))
 (drop : Except I Unit → Op S Unit) (s t : S) (es : List Event) (e : I)
 (h : write s = ⟨es,t,.value (.error e)⟩) :
 ignoredWrite write drop s = prepend es (drop (.error e) t) := by
 simp only [ignoredWrite,sequence,h,bind]'''),
th('''theorem report_error_normal (e : E) (r d : E → Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t u : S) (rs ds : List Event)
 (hr : r e s = ⟨rs,t,.value ()⟩) (hd : d e t = ⟨ds,u,.value ()⟩) :
 reportOwned (.error e) r d dp s = ⟨rs++ds,u,.value 1⟩ := by
 simp [reportOwned,sequence,normal_drop_order () s t u rs ds (r e) (d e) dp hr hd,
 bind,prepend,pure]'''),
th('''theorem report_abort_no_error_drop (e : E) (r d : E → Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t : S) (es : List Event) (c : Crash)
 (h : r e s = ⟨es,t,.abort c⟩) :
 reportOwned (.error e) r d dp s = ⟨es,t,.abort c⟩ := by
 simp [reportOwned,sequence,scope_abort_no_cleanup es s t c (r e) (d e) dp h,bind]'''),
th('''theorem report_diverge_no_error_drop (e : E) (r d : E → Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t : S) (es : List Event)
 (h : r e s = ⟨es,t,.diverge⟩) :
 reportOwned (.error e) r d dp s = ⟨es,t,.diverge⟩ := by
 simp [reportOwned,sequence,scope_diverge_no_cleanup es s t (r e) (d e) dp h,bind]'''),
th('''theorem report_panic_keeps_cleanup (e : E) (r d : E → Op S Unit)
 (dp : Panic → Panic → Op S Unit) (s t : S) (es : List Event) (p : Panic)
 (h : r e s = ⟨es,t,.panic p⟩) :
 reportOwned (.error e) r d dp s =
 bind (prepend es (unwind p (d e) dp t)) (fun _ => pure 1) := by
 simp only [reportOwned,sequence,scope_panic es s t p (r e) (d e) dp h]''')])

def write_plans():
 (E/'proof-plans.json').write_text(json.dumps(plans,indent=2)+'\n')
if __name__=='__main__':
 write_plans()
 for name,p in plans.items():
  s='\n'.join('import '+i for i in p['imports'])+'\n'+p['base']+'\n\n'+'\n\n'.join(p['steps'])+'\nend PV_DIAG3\n'
  if '--check' in sys.argv:assert (E/(name+'.lean')).read_text()==s
  else:(E/(name+'.lean')).write_text(s)
