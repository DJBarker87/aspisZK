module('Open','import PV_DIAG12_WriteAll',[
'''structure OpenOptions where
 read : Bool := false
 write : Bool := false
 append : Bool := false
 truncate : Bool := false
 create : Bool := false
 createNew : Bool := false
 custom : Nat := 0
 mode : Nat := 438
 deriving DecidableEq, Repr
inductive Validation where
 | needsWrite | needsAccess
 deriving DecidableEq, Repr
def access (o : OpenOptions) : Except Validation Nat :=
 match o.read,o.write,o.append with
 | true,false,false => .ok 0
 | false,true,false => .ok 1
 | true,true,false => .ok 2
 | false,_,true => .ok 1025
 | true,_,true => .ok 1026
 | false,false,false =>
   if o.create || o.createNew || o.truncate then .error .needsWrite else .error .needsAccess
def creation (o : OpenOptions) : Except Validation Nat :=
 if (!o.write && !o.append && (o.truncate || o.create || o.createNew)) ||
     (o.append && o.truncate && !o.createNew) then .error .needsWrite else
 .ok (if o.createNew then 192 else (if o.create then 64 else 0)+(if o.truncate then 512 else 0))
def openFlags (o : OpenOptions) : Except Validation Nat := do
 let a ← access o
 let c ← creation o
 pure (Nat.lor 524288 (Nat.lor a (Nat.lor c (Nat.land o.custom 4294967292))))
/- custom is the u32 representation of c_int. Restrict custom<2^32 and
mode<2^32 at the native representation boundary; no saturation is substituted. -/
theorem open_default_invalid : access {}=.error .needsAccess := rfl''',
'''theorem open_read_access (o : OpenOptions) (hr : o.read=true) (hw : o.write=false)
 (ha : o.append=false) : access o=.ok 0 := by simp only [access,hr,hw,ha]''',
'''theorem open_write_access (o : OpenOptions) (hr : o.read=false) (hw : o.write=true)
 (ha : o.append=false) : access o=.ok 1 := by simp only [access,hr,hw,ha]''',
'''theorem open_readwrite_access (o : OpenOptions) (hr : o.read=true) (hw : o.write=true)
 (ha : o.append=false) : access o=.ok 2 := by simp only [access,hr,hw,ha]''',
'''theorem open_append_access (o : OpenOptions) (hr : o.read=false) (ha : o.append=true) :
 access o=.ok 1025 := by cases h : o.write <;> simp only [access,hr,h,ha]
theorem open_readappend_access (o : OpenOptions) (hr : o.read=true) (ha : o.append=true) :
 access o=.ok 1026 := by cases h : o.write <;> simp only [access,hr,h,ha]''',
'''def openRetry (q : Request) (sig : Signal) : Nat → Cursor → WRun Nat
 | 0,c => ⟨⟨[],.cut⟩,c⟩
 | fuel+1,c =>
  let reply := sig c.next q
  let r := call q reply
  let c' : Cursor := ⟨c.next+1⟩
  match reply with
  | .error e => if e=4 then
      let tail := openRetry q sig fuel c'
      ⟨⟨r.trace++tail.execution.trace,tail.execution.result⟩,tail.cursor⟩
     else ⟨r,c'⟩
  | _ => ⟨r,c'⟩
def openC (addr : Nat) (path : Bytes) (o : OpenOptions) (sig : Signal)
 (fuel : Nat) (c : Cursor) : Except Validation (WRun Nat) :=
 match openFlags o with
 | .error e => .error e
 | .ok flags => .ok (openRetry (.open64 addr path flags o.mode) sig fuel c)
theorem open_retry_cut (q : Request) (sig : Signal) (c : Cursor) :
 openRetry q sig 0 c=⟨⟨[],.cut⟩,c⟩ := rfl''',
'''theorem open_retry_eintr (q : Request) (sig : Signal) (fuel : Nat) (c : Cursor)
 (h : sig c.next q=.error 4) :
 openRetry q sig (fuel+1) c=
 let tail := openRetry q sig fuel ⟨c.next+1⟩
 ⟨⟨⟨q,.error 4⟩::tail.execution.trace,tail.execution.result⟩,tail.cursor⟩ := by
 simp only [openRetry,h,call,eq_self,ite_true,List.cons_append,List.nil_append]''',
'''theorem open_retry_error (q : Request) (sig : Signal) (fuel : Nat) (c : Cursor)
 (e : Int) (h : sig c.next q=.error e) (he : e≠4) :
 openRetry q sig (fuel+1) c=⟨⟨[⟨q,.error e⟩],.error e⟩,⟨c.next+1⟩⟩ := by
 simp only [openRetry,h,call,if_neg he]''',
'''theorem open_retry_ok (q : Request) (sig : Signal) (fuel : Nat) (c : Cursor)
 (n : Nat) (h : sig c.next q=.returned n) :
 openRetry q sig (fuel+1) c=⟨⟨[⟨q,.returned n⟩],.ok n⟩,⟨c.next+1⟩⟩ := by
 simp only [openRetry,h,call]''',
'''theorem open_rejected_before_request (addr : Nat) (path : Bytes) (o : OpenOptions)
 (sig : Signal) (fuel : Nat) (c : Cursor) (e : Validation) (h : openFlags o=.error e) :
 openC addr path o sig fuel c=.error e := by simp only [openC,h]''',
])
module('Buffer','import PV_DIAG12_Open',[
'''structure Buffer where
 span : Span
 capacity : Nat
 panicked : Bool
 deriving DecidableEq, Repr
structure BRun (A : Type) where
 execution : Exec A
 buffer : Buffer
 cursor : Cursor
 deriving DecidableEq, Repr
def pureB {A : Type} (a : A) (b : Buffer) (c : Cursor) : BRun A := ⟨pureE a,b,c⟩
def bindB {A B : Type} (r : BRun A) (f : A → Buffer → Cursor → BRun B) : BRun B :=
 match r.execution.result with
 | .ok a => let s := f a r.buffer r.cursor
            ⟨⟨r.execution.trace++s.execution.trace,s.execution.result⟩,s.buffer,s.cursor⟩
 | .error e => ⟨⟨r.execution.trace,.error e⟩,r.buffer,r.cursor⟩
 | .cut => ⟨⟨r.execution.trace,.cut⟩,r.buffer,r.cursor⟩
def spare (b : Buffer) : Nat := b.capacity-b.span.bytes.length
def appendBuffer (b : Buffer) (xs : Bytes) : Buffer :=
 {b with span := {b.span with bytes := b.span.bytes++xs}}
def flushLoop (w : Writer) (q : Span → Request) (sig : Signal) :
 Nat → Buffer → Cursor → BRun Unit
 | 0,b,c => ⟨⟨[],.cut⟩,b,c⟩
 | fuel+1,b,c =>
  if b.span.bytes.isEmpty then pureB () b c else
  let r := w b.span (sig c.next (q b.span))
  let c' : Cursor := ⟨c.next+1⟩
  match r.result with
  | .cut => ⟨⟨r.trace,.cut⟩,{b with panicked := true},c'⟩
  | .error e =>
   if e=4 then
    let tail := flushLoop w q sig fuel {b with panicked := false} c'
    ⟨⟨r.trace++tail.execution.trace,tail.execution.result⟩,tail.buffer,tail.cursor⟩
   else ⟨⟨r.trace,.error e⟩,{b with panicked := false},c'⟩
  | .ok n =>
   if n=0 then ⟨⟨r.trace,.error (-1)⟩,{b with panicked := false},c'⟩ else
   if n>b.span.bytes.length then ⟨⟨r.trace,.error (-2)⟩,{b with panicked := false},c'⟩ else
   let tail := flushLoop w q sig fuel {b with span := advance b.span n,panicked := false} c'
   ⟨⟨r.trace++tail.execution.trace,tail.execution.result⟩,tail.buffer,tail.cursor⟩
/- flushLoop models the remaining slice of the live BufGuard. flushBuf rebases
the resulting content after ordinary-return Vec::drain. Exact intermediate
Vec memory, native unwind and pointer restoration still require association. -/
theorem flush_cut (w : Writer) (q : Span → Request) (sig : Signal) (b : Buffer) (c : Cursor) :
 flushLoop w q sig 0 b c=⟨⟨[],.cut⟩,b,c⟩ := rfl''',
'''theorem bindB_error {A B : Type} (es : List Exchange) (e : Int) (b : Buffer) (c : Cursor)
 (f : A → Buffer → Cursor → BRun B) :
 bindB ⟨⟨es,.error e⟩,b,c⟩ f=⟨⟨es,.error e⟩,b,c⟩ := rfl''',
'''theorem bindB_cut {A B : Type} (es : List Exchange) (b : Buffer) (c : Cursor)
 (f : A → Buffer → Cursor → BRun B) :
 bindB ⟨⟨es,.cut⟩,b,c⟩ f=⟨⟨es,.cut⟩,b,c⟩ := rfl''',
'''theorem bindB_pure {A B : Type} (a : A) (b : Buffer) (c : Cursor)
 (f : A → Buffer → Cursor → BRun B) : bindB (pureB a b c) f=f a b c := by
 simp only [bindB,pureB,pureE,List.nil_append]''',
'''theorem flush_empty (w : Writer) (q : Span → Request) (sig : Signal) (fuel : Nat)
 (b : Buffer) (c : Cursor) (h : b.span.bytes.isEmpty=true) :
 flushLoop w q sig (fuel+1) b c=pureB () b c := by
 simp only [flushLoop,h,eq_self,ite_true]''',
'''theorem flush_error (w : Writer) (q : Span → Request) (sig : Signal) (fuel : Nat)
 (b : Buffer) (c : Cursor) (h : b.span.bytes.isEmpty=false)
 (es : List Exchange) (e : Int) (hr : w b.span (sig c.next (q b.span))=⟨es,.error e⟩) (he : e≠4) :
 flushLoop w q sig (fuel+1) b c=⟨⟨es,.error e⟩,{b with panicked := false},⟨c.next+1⟩⟩ := by
 simp only [flushLoop,h,Bool.false_eq_true,ite_false,hr,if_neg he]''',
'''theorem flush_interrupted (w : Writer) (q : Span → Request) (sig : Signal) (fuel : Nat)
 (b : Buffer) (c : Cursor) (h : b.span.bytes.isEmpty=false)
 (es : List Exchange) (hr : w b.span (sig c.next (q b.span))=⟨es,.error 4⟩) :
 flushLoop w q sig (fuel+1) b c=
 let tail := flushLoop w q sig fuel {b with panicked := false} ⟨c.next+1⟩
 ⟨⟨es++tail.execution.trace,tail.execution.result⟩,tail.buffer,tail.cursor⟩ := by
 simp only [flushLoop,h,Bool.false_eq_true,ite_false,hr,eq_self,ite_true]''',
'''theorem flush_zero (w : Writer) (q : Span → Request) (sig : Signal) (fuel : Nat)
 (b : Buffer) (c : Cursor) (h : b.span.bytes.isEmpty=false)
 (es : List Exchange) (hr : w b.span (sig c.next (q b.span))=⟨es,.ok 0⟩) :
 flushLoop w q sig (fuel+1) b c=⟨⟨es,.error (-1)⟩,{b with panicked := false},⟨c.next+1⟩⟩ := by
 simp only [flushLoop,h,Bool.false_eq_true,ite_false,hr,eq_self,ite_true]''',
'''theorem flush_progress (w : Writer) (q : Span → Request) (sig : Signal) (fuel : Nat)
 (b : Buffer) (c : Cursor) (h : b.span.bytes.isEmpty=false)
 (es : List Exchange) (n : Nat) (hr : w b.span (sig c.next (q b.span))=⟨es,.ok n⟩)
 (hn : n≠0) (hb : ¬ n>b.span.bytes.length) :
 flushLoop w q sig (fuel+1) b c=
 let tail := flushLoop w q sig fuel {b with span := advance b.span n,panicked := false} ⟨c.next+1⟩
 ⟨⟨es++tail.execution.trace,tail.execution.result⟩,tail.buffer,tail.cursor⟩ := by
 simp only [flushLoop,h,Bool.false_eq_true,ite_false,hr,if_neg hn,if_neg hb]''',
'''theorem flush_missing_return (w : Writer) (q : Span → Request) (sig : Signal) (fuel : Nat)
 (b : Buffer) (c : Cursor) (h : b.span.bytes.isEmpty=false)
 (es : List Exchange) (hr : w b.span (sig c.next (q b.span))=⟨es,.cut⟩) :
 flushLoop w q sig (fuel+1) b c=⟨⟨es,.cut⟩,{b with panicked := true},⟨c.next+1⟩⟩ := by
 simp only [flushLoop,h,Bool.false_eq_true,ite_false,hr]''',
'''def rebaseBuffer (original view : Buffer) : Buffer :=
 {view with span := {view.span with base := original.span.base,offset := original.span.offset}}
def flushBuf (w : Writer) (q : Span → Request) (sig : Signal)
 (fuel : Nat) (b : Buffer) (c : Cursor) : BRun Unit :=
 let r := flushLoop w q sig fuel b c
 match r.execution.result with
 | .cut => r
 | _ => {r with buffer := rebaseBuffer b r.buffer}
theorem rebase_preserves_content (b view : Buffer) :
 (rebaseBuffer b view).span.bytes=view.span.bytes := rfl
theorem rebase_restores_offset (b view : Buffer) :
 (rebaseBuffer b view).span.offset=b.span.offset := rfl''',
'''def writeToBuf (b : Buffer) (xs : Bytes) (c : Cursor) : BRun Nat :=
 ⟨pureE (min (spare b) xs.length),appendBuffer b (xs.take (min (spare b) xs.length)),c⟩
theorem buffered_append_bytes (b : Buffer) (xs : Bytes) :
 (appendBuffer b xs).span.bytes=b.span.bytes++xs := rfl''',
'''theorem buffered_append_capacity (b : Buffer) (xs : Bytes) :
 (appendBuffer b xs).capacity=b.capacity := rfl
theorem buffered_append_panicked (b : Buffer) (xs : Bytes) :
 (appendBuffer b xs).panicked=b.panicked := rfl''',
'''def directAll (fd : Int) (sig : Signal) (fuel : Nat) (s : Span) (b : Buffer) (c : Cursor) : BRun Unit :=
 let r := stdWriteAll fd sig fuel s c
 ⟨r.execution,b,r.cursor⟩
def bufferedAll (fd : Int) (sig : Signal) (fuel : Nat) (s : Span) (b : Buffer) (c : Cursor) : BRun Unit :=
 if s.bytes.length<spare b then pureB () (appendBuffer b s.bytes) c else
 let r := if s.bytes.length>spare b then flushBuf (stdWrite fd) (writeRequest fd) sig fuel b c else pureB () b c
 bindB r fun _ b c =>
  if s.bytes.length≥b.capacity then
   let r := directAll fd sig fuel s b c
   {r with buffer := {r.buffer with panicked := match r.execution.result with | .cut => true | _ => false}}
  else pureB () (appendBuffer b s.bytes) c
theorem bufferedAll_fits (fd : Int) (sig : Signal) (fuel : Nat) (s : Span) (b : Buffer) (c : Cursor)
 (h : s.bytes.length<spare b) :
 bufferedAll fd sig fuel s b c=pureB () (appendBuffer b s.bytes) c := by
 simp only [bufferedAll,if_pos h]''',
'''theorem bufferedAll_fits_no_request (fd : Int) (sig : Signal) (fuel : Nat) (s : Span) (b : Buffer) (c : Cursor)
 (h : s.bytes.length<spare b) :
 (bufferedAll fd sig fuel s b c).execution.trace=[] := by
 rw [bufferedAll_fits fd sig fuel s b c h]; rfl''',
'''def bufferDrop (fd : Int) (sig : Signal) (fuel : Nat) (b : Buffer) (c : Cursor) : BRun Unit :=
 if b.panicked then pureB () b c else
 let r := flushBuf (stdWrite fd) (writeRequest fd) sig fuel b c
 {r with execution := ⟨r.execution.trace,match r.execution.result with | .cut => .cut | _ => .ok ()⟩}
theorem bufferDrop_panicked (fd : Int) (sig : Signal) (fuel : Nat) (b : Buffer) (c : Cursor)
 (h : b.panicked=true) : bufferDrop fd sig fuel b c=pureB () b c := by
 simp only [bufferDrop,h,eq_self,ite_true]''',
'''theorem bufferDrop_trace (fd : Int) (sig : Signal) (fuel : Nat) (b : Buffer) (c : Cursor)
 (h : b.panicked=false) :
 (bufferDrop fd sig fuel b c).execution.trace=(flushBuf (stdWrite fd) (writeRequest fd) sig fuel b c).execution.trace := by
 simp only [bufferDrop,h,Bool.false_eq_true,ite_false]''',
'''theorem bufferDrop_error_ignored (fd : Int) (sig : Signal) (fuel : Nat) (b : Buffer) (c : Cursor)
 (e : Int) (hp : b.panicked=false)
 (h : (flushBuf (stdWrite fd) (writeRequest fd) sig fuel b c).execution.result=.error e) :
 (bufferDrop fd sig fuel b c).execution.result=.ok () := by
 simp only [bufferDrop,hp,Bool.false_eq_true,ite_false,h]''',
'''theorem bufferDrop_cut_kept (fd : Int) (sig : Signal) (fuel : Nat) (b : Buffer) (c : Cursor)
 (hp : b.panicked=false)
 (h : (flushBuf (stdWrite fd) (writeRequest fd) sig fuel b c).execution.result=.cut) :
 (bufferDrop fd sig fuel b c).execution.result=.cut := by
 simp only [bufferDrop,hp,Bool.false_eq_true,ite_false,h]''',
])
