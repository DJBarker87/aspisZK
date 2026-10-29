from pathlib import Path
import json,re,hashlib
D=Path(__file__).resolve().parent
plans=[]
def module(name,header,steps):
 text=header+'\nnamespace PV_DIAG12\nset_option autoImplicit false\n'
 for chunk in steps:
  text+='\n'+chunk+'\n'
  # Print every newly added theorem; all previous remain audited too.
  for n in re.findall(r'^theorem (\w+)',chunk,re.M):text+='#print axioms '+n+'\n'
  src=text+'\nend PV_DIAG12\n'
  plans.append(dict(module='PV_DIAG12_'+name,source=src,sha256=hashlib.sha256(src.encode()).hexdigest()))
 (D/('PV_DIAG12_'+name+'.lean')).write_text(src)
module('Boundary','import Init',[
'''/-! Linux x86_64 std-to-POSIX-ABI request semantics. `Exchange` names the
foreign call, NOT its unproved libc-to-kernel expansion. `cut` is an observation
boundary, never a claim of divergence. Pointer coordinates remain observable. -/
abbrev Bytes := List UInt8
structure Span where
 base : Nat
 offset : Nat
 bytes : Bytes
 deriving DecidableEq, Repr
def advance (s : Span) (n : Nat) : Span :=
 ⟨s.base,s.offset+n,s.bytes.drop n⟩
inductive Request where
 | write (fd : Int) (span : Span) (count : Nat)
 | open64 (pathAddress : Nat) (path : Bytes) (flags mode : Nat)
 | close (fd : Int)
 deriving DecidableEq, Repr
inductive Reply where
 | returned (value : Nat)
 | error (errno : Int)
 | cut
 deriving DecidableEq, Repr
structure Exchange where
 request : Request
 reply : Reply
 deriving DecidableEq, Repr
inductive Result (A : Type) where
 | ok (value : A)
 | error (errno : Int)
 | cut
 deriving DecidableEq, Repr
structure Exec (A : Type) where
 trace : List Exchange
 result : Result A
 deriving DecidableEq, Repr
def pureE {A : Type} (a : A) : Exec A := ⟨[],.ok a⟩
def bindE {A B : Type} (r : Exec A) (f : A → Exec B) : Exec B :=
 match r.result with
 | .ok a => let s := f a; ⟨r.trace++s.trace,s.result⟩
 | .error e => ⟨r.trace,.error e⟩
 | .cut => ⟨r.trace,.cut⟩
def call (q : Request) (r : Reply) : Exec Nat :=
 ⟨[⟨q,r⟩],match r with | .returned n => .ok n | .error e => .error e | .cut => .cut⟩
theorem call_request (q : Request) (r : Reply) : (call q r).trace.map Exchange.request=[q] := rfl''',
'''theorem advance_zero (s : Span) : advance s 0=s := by cases s; rfl
theorem advance_add (s : Span) (a b : Nat) : advance (advance s a) b=advance s (a+b) := by
 cases s; simp only [advance,List.drop_drop,Nat.add_assoc]''',
'''theorem bind_ok {A B : Type} (es : List Exchange) (a : A) (f : A → Exec B) :
 bindE ⟨es,.ok a⟩ f=⟨es++(f a).trace,(f a).result⟩ := rfl
theorem bind_error {A B : Type} (es : List Exchange) (e : Int) (f : A → Exec B) :
 bindE ⟨es,.error e⟩ f=⟨es,.error e⟩ := rfl''',
'''theorem bind_cut {A B : Type} (es : List Exchange) (f : A → Exec B) :
 bindE ⟨es,.cut⟩ f=⟨es,.cut⟩ := rfl
theorem bind_pure {A B : Type} (a : A) (f : A → Exec B) : bindE (pureE a) f=f a := by
 simp only [bindE,pureE,List.nil_append]''',
'''theorem bind_prefix {A B : Type} (r : Exec A) (f : A → Exec B) :
 ∃ tail, (bindE r f).trace=r.trace++tail := by
 cases r with | mk es ex => cases ex <;> simp only [bindE] <;>
   first | exact ⟨_,rfl⟩ | exact ⟨[],(List.append_nil _).symm⟩''',
'''theorem bind_assoc {A B C : Type} (r : Exec A) (f : A → Exec B) (g : B → Exec C) :
 bindE (bindE r f) g=bindE r (fun a => bindE (f a) g) := by
 cases r with
 | mk es ex =>
  cases ex with
  | ok a => cases h : f a with
    | mk fs fx => cases fx <;> simp only [bindE,h,List.append_assoc]
  | error e => rfl
  | cut => rfl''',
'''def requested (es : List Exchange) : List Request := es.map Exchange.request
def delivered (fd : Int) (es : List Exchange) : Bytes := es.flatMap fun e =>
 match e.request,e.reply with
 | .write out s count,.returned n => if out=fd then s.bytes.take (min count n) else []
 | _,_ => []
theorem delivered_append (fd : Int) (xs ys : List Exchange) :
 delivered fd (xs++ys)=delivered fd xs++delivered fd ys := by
 simp only [delivered,List.flatMap_append]''',
'''theorem delivered_error (fd out : Int) (s : Span) (count : Nat) (e : Int) :
 delivered fd [⟨.write out s count,.error e⟩]=[] := rfl
theorem delivered_cut (fd out : Int) (s : Span) (count : Nat) :
 delivered fd [⟨.write out s count,.cut⟩]=[] := rfl''',
'''theorem delivered_write (fd : Int) (s : Span) (count n : Nat) :
 delivered fd [⟨.write fd s count,.returned n⟩]=s.bytes.take (min count n) := by
 simp only [delivered,eq_self,ite_true,List.flatMap_cons,List.flatMap_nil,List.append_nil]''',
'''theorem requested_append (xs ys : List Exchange) :
 requested (xs++ys)=requested xs++requested ys := by
 simp only [requested,List.map_append]
theorem advance_base (s : Span) (n : Nat) : (advance s n).base=s.base := rfl''',
])
module('Fd','import PV_DIAG12_Boundary',[
'''def linuxReadLimit : Nat := 9223372036854775807
def fdWrite (fd : Int) (s : Span) (r : Reply) : Exec Nat :=
 call (.write fd s (min s.bytes.length linuxReadLimit)) r
def fdFlush : Exec Unit := pureE ()
/- OwnedFd::drop ignores close's result, without retry or cvt/errno read.
A cut is still a missing return, not ordinary completion. -/
def fdDrop (fd : Int) (r : Reply) : Exec Unit :=
 ⟨[⟨.close fd,r⟩],match r with | .cut => .cut | _ => .ok ()⟩
theorem fd_write_request (fd : Int) (s : Span) (r : Reply) :
 requested (fdWrite fd s r).trace=[.write fd s (min s.bytes.length linuxReadLimit)] := rfl''',
'''theorem fd_write_count_bounded (fd : Int) (s : Span) (r : Reply) :
 (fdWrite fd s r).trace=[⟨.write fd s (min s.bytes.length linuxReadLimit),r⟩] := rfl
theorem fd_flush_no_fsync : fdFlush=⟨[],.ok ()⟩ := rfl''',
'''theorem fd_drop_error_not_retried (fd e : Int) :
 fdDrop fd (.error e)=⟨[⟨.close fd,.error e⟩],.ok ()⟩ := rfl
theorem fd_drop_success (fd : Int) (n : Nat) :
 fdDrop fd (.returned n)=⟨[⟨.close fd,.returned n⟩],.ok ()⟩ := rfl''',
'''def maskBadFd {A : Type} (fallback : A) (r : Exec A) : Exec A :=
 ⟨r.trace,match r.result with | .error e => if e=9 then .ok fallback else .error e | x => x⟩
def stdWrite (fd : Int) (s : Span) (r : Reply) : Exec Nat :=
 maskBadFd s.bytes.length (fdWrite fd s r)
theorem mask_preserves_requests {A : Type} (a : A) (r : Exec A) :
 (maskBadFd a r).trace=r.trace := rfl''',
'''theorem std_ebadf_accepted (fd : Int) (s : Span) :
 (stdWrite fd s (.error 9)).result=.ok s.bytes.length := by
 simp only [stdWrite,maskBadFd,fdWrite,call,eq_self,ite_true]
theorem std_ebadf_not_delivered (fd : Int) (s : Span) :
 delivered fd (stdWrite fd s (.error 9)).trace=[] := rfl''',
'''theorem std_other_error (fd e : Int) (s : Span) (h : e≠9) :
 (stdWrite fd s (.error e)).result=.error e := by
 simp only [stdWrite,maskBadFd,fdWrite,call,if_neg h]
theorem std_write_success (fd : Int) (s : Span) (n : Nat) :
 (stdWrite fd s (.returned n)).result=.ok n := rfl''',
'''theorem std_cut (fd : Int) (s : Span) :
 (stdWrite fd s .cut).result=.cut := rfl
theorem std_write_trace (fd : Int) (s : Span) (r : Reply) :
 (stdWrite fd s r).trace=(fdWrite fd s r).trace := rfl''',
'''def stdoutWrite := stdWrite 1
def stderrWrite := stdWrite 2
theorem stdout_request (s : Span) (r : Reply) :
 requested (stdoutWrite s r).trace=[.write 1 s (min s.bytes.length linuxReadLimit)] := rfl
theorem stderr_request (s : Span) (r : Reply) :
 requested (stderrWrite s r).trace=[.write 2 s (min s.bytes.length linuxReadLimit)] := rfl''',
'''theorem fd_drop_cut (fd : Int) :
 fdDrop fd .cut=⟨[⟨.close fd,.cut⟩],.cut⟩ := rfl
theorem no_close_stdout (s : Span) (r : Reply) :
 ∀ e ∈ (stdoutWrite s r).trace, e.request≠.close 1 := by
 intro e h; simp only [stdoutWrite,stdWrite,maskBadFd,fdWrite,call,List.mem_singleton] at h
 cases h; intro h; cases h''',
])
# write_all has a cursor indexed by completed ABI calls, so retries cannot reset signal.
module('WriteAll','import PV_DIAG12_Fd',[
'''structure Cursor where
 next : Nat
 deriving DecidableEq, Repr
structure WRun (A : Type) where
 execution : Exec A
 cursor : Cursor
 deriving DecidableEq, Repr
abbrev Signal := Nat → Request → Reply
abbrev Writer := Span → Reply → Exec Nat
def writeAll (write : Writer) (request : Span → Request) (signal : Signal) :
 Nat → Span → Cursor → WRun Unit
 | 0,_,c => ⟨⟨[],.cut⟩,c⟩
 | fuel+1,s,c =>
  if s.bytes.isEmpty then ⟨pureE (),c⟩ else
  let r := write s (signal c.next (request s))
  let c' : Cursor := ⟨c.next+1⟩
  match r.result with
  | .cut => ⟨⟨r.trace,.cut⟩,c'⟩
  | .error e =>
    if e=4 then
     let tail := writeAll write request signal fuel s c'
     ⟨⟨r.trace++tail.execution.trace,tail.execution.result⟩,tail.cursor⟩
    else ⟨⟨r.trace,.error e⟩,c'⟩
  | .ok n =>
    if n=0 then ⟨⟨r.trace,.error (-1)⟩,c'⟩ else
    if n>s.bytes.length then ⟨⟨r.trace,.error (-2)⟩,c'⟩ else
    let tail := writeAll write request signal fuel (advance s n) c'
    ⟨⟨r.trace++tail.execution.trace,tail.execution.result⟩,tail.cursor⟩
/- -1 and -2 are MODEL errors: WriteZero and invalid Write contract.
They are not OS errno values and do not identify a native panic/hook. -/
theorem writeAll_cut (w : Writer) (q : Span → Request) (sig : Signal) (s : Span) (c : Cursor) :
 writeAll w q sig 0 s c=⟨⟨[],.cut⟩,c⟩ := rfl''',
'''theorem writeAll_empty (w : Writer) (q : Span → Request) (sig : Signal)
 (fuel : Nat) (s : Span) (c : Cursor) (h : s.bytes.isEmpty=true) :
 writeAll w q sig (fuel+1) s c=⟨pureE (),c⟩ := by simp only [writeAll,h,eq_self,ite_true]''',
'''theorem writeAll_error (w : Writer) (q : Span → Request) (sig : Signal)
 (fuel : Nat) (s : Span) (c : Cursor) (h : s.bytes.isEmpty=false)
 (es : List Exchange) (e : Int) (hr : w s (sig c.next (q s))=⟨es,.error e⟩) (he : e≠4) :
 writeAll w q sig (fuel+1) s c=⟨⟨es,.error e⟩,⟨c.next+1⟩⟩ := by
 simp only [writeAll,h,Bool.false_eq_true,ite_false,hr,if_neg he]''',
'''theorem writeAll_interrupted (w : Writer) (q : Span → Request) (sig : Signal)
 (fuel : Nat) (s : Span) (c : Cursor) (h : s.bytes.isEmpty=false)
 (es : List Exchange) (hr : w s (sig c.next (q s))=⟨es,.error 4⟩) :
 writeAll w q sig (fuel+1) s c=
 let tail := writeAll w q sig fuel s ⟨c.next+1⟩
 ⟨⟨es++tail.execution.trace,tail.execution.result⟩,tail.cursor⟩ := by
 simp only [writeAll,h,Bool.false_eq_true,ite_false,hr,eq_self,ite_true]''',
'''theorem writeAll_zero (w : Writer) (q : Span → Request) (sig : Signal)
 (fuel : Nat) (s : Span) (c : Cursor) (h : s.bytes.isEmpty=false)
 (es : List Exchange) (hr : w s (sig c.next (q s))=⟨es,.ok 0⟩) :
 writeAll w q sig (fuel+1) s c=⟨⟨es,.error (-1)⟩,⟨c.next+1⟩⟩ := by
 simp only [writeAll,h,Bool.false_eq_true,ite_false,hr,eq_self,ite_true]''',
'''theorem writeAll_progress (w : Writer) (q : Span → Request) (sig : Signal)
 (fuel : Nat) (s : Span) (c : Cursor) (h : s.bytes.isEmpty=false)
 (es : List Exchange) (n : Nat) (hr : w s (sig c.next (q s))=⟨es,.ok n⟩)
 (hn : n≠0) (hb : ¬ n>s.bytes.length) :
 writeAll w q sig (fuel+1) s c=
 let tail := writeAll w q sig fuel (advance s n) ⟨c.next+1⟩
 ⟨⟨es++tail.execution.trace,tail.execution.result⟩,tail.cursor⟩ := by
 simp only [writeAll,h,Bool.false_eq_true,ite_false,hr,if_neg hn,if_neg hb]''',
'''theorem writeAll_missing_return (w : Writer) (q : Span → Request) (sig : Signal)
 (fuel : Nat) (s : Span) (c : Cursor) (h : s.bytes.isEmpty=false)
 (es : List Exchange) (hr : w s (sig c.next (q s))=⟨es,.cut⟩) :
 writeAll w q sig (fuel+1) s c=⟨⟨es,.cut⟩,⟨c.next+1⟩⟩ := by
 simp only [writeAll,h,Bool.false_eq_true,ite_false,hr]''',
'''def writeRequest (fd : Int) (s : Span) : Request := .write fd s (min s.bytes.length linuxReadLimit)
def fdWriteAll (fd : Int) := writeAll (fdWrite fd) (writeRequest fd)
/- The EBADF mask encloses sys::stdio::write_all ONCE; masking each write
inside its loop would alter the request sequence after a partial write. -/
def stdWriteAll (fd : Int) (sig : Signal) (fuel : Nat) (s : Span) (c : Cursor) : WRun Unit :=
 let r := fdWriteAll fd sig fuel s c
 ⟨maskBadFd () r.execution,r.cursor⟩
theorem std_all_trace (fd : Int) (sig : Signal) (fuel : Nat) (s : Span) (c : Cursor) :
 (stdWriteAll fd sig fuel s c).execution.trace=(fdWriteAll fd sig fuel s c).execution.trace := rfl''',
'''theorem std_all_ebadf (fd : Int) (sig : Signal) (fuel : Nat) (s : Span) (c : Cursor)
 (h : (fdWriteAll fd sig fuel s c).execution.result=.error 9) :
 (stdWriteAll fd sig fuel s c).execution.result=.ok () := by
 simp only [stdWriteAll,maskBadFd,h,eq_self,ite_true]''',
'''theorem std_all_preserves_cursor (fd : Int) (sig : Signal) (fuel : Nat) (s : Span) (c : Cursor) :
 (stdWriteAll fd sig fuel s c).cursor=(fdWriteAll fd sig fuel s c).cursor := rfl
theorem std_all_error_deliveries (fd : Int) (sig : Signal) (fuel : Nat) (s : Span) (c : Cursor) :
 delivered fd (stdWriteAll fd sig fuel s c).execution.trace=
 delivered fd (fdWriteAll fd sig fuel s c).execution.trace := rfl''',
])
exec((D/'parts.py').read_text())
(D/'plans.json').write_text(json.dumps(plans,indent=2)+'\n')
print(len(plans),'stages')
