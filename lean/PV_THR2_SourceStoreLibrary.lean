import PV_THR2_SourceStoreNative
set_option autoImplicit false
noncomputable section
namespace PV_THR2_SourceStoreLibrary
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_THR2_SourceStoreNative
local instance : DecidableEq Data := Classical.decEq Data

/-- Value-level information at the native boundary. Reserve's result is the
RawVec after its actual allocation/growth, not a source Store or a delta.
Pointer operations retain their representation/provenance. Binding these
values to the pinned runtime/OWNER allocator is separate from Store dispatch;
an arbitrary instance of this record is NOT a source-adequacy theorem. -/
structure Values (W E : Type) where
  width : Data → Nat
  rawNonNull : Data → Option Data
  addNonNull : Data → Nat → Option Data
  subPointer : Data → Nat → Option Data
  reserve : Data → Data → Nat → Nat → W → Reply W E Data → Option Data

def withField (p : Address) (field : Nat) : Address :=
  {p with fields := p.fields ++ [field]}

def receiver {W : Type} (C : Carrier W Data) (s : Store Data)
    (w : W) (reference : Data) : Option (Address × Data) := do
  let p ← C.dereference w reference
  let value ← readAddress C s p
  pure (p,value)

/-- D959, exact emitted f289, core/src/cell.rs:510 on the pinned 1.94.1
source (body/file SHA in session15/store-write-source.json). Cell::replace
calls mem::replace on self.value.get(): replace the addressed value, not every
reachable root. The transparent Cell<bool> representation is the existing
f207 carrier's scalar bool representation. No backend Store is accepted.
https://doc.rust-lang.org/std/cell/struct.Cell.html#method.replace -/
def PV_THR2_LibrarySemantics_CellReplace289 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  match args with
  | [reference,value] =>
    let p ← C.dereference w reference
    writeAddress C s p (some value)
  | _ => none

/-- f93: core/src/iter/range.rs:856 -> specialized spec_next:771,
Range<usize>, source hashes in session15. Increment start exactly when start
is below end. The exhausted case performs no write. This operation does not
invent the returned Option value or alter the full reply.
https://doc.rust-lang.org/std/ops/struct.Range.html -/
def PV_THR2_LibrarySemantics_RangeNext93 {W : Type} (C : Carrier W Data)
    (args : List Data) (s : Store Data) (w : W) : Option (Store Data) := do
  match args with
  | [reference] =>
    let (p,value) ← receiver C s w reference
    let .number start ← C.field value 0 | none
    let .number finish ← C.field value 1 | none
    if start < finish then
      writeAddress C s (withField p 0) (some (.number (start+1)))
    else pure s
  | _ => none

/-- f9: alloc/src/vec/into_iter.rs:214, pinned body in session15.
The LLBC IntoIter fields are ptr=4,end=5 (not buf=0). For a non-ZST advance
ptr by sizeof(T); for a ZST preserve ptr and reduce end by one byte. Exhaustion
does not write. The pointee read is in the existing native world reply.
https://doc.rust-lang.org/std/vec/struct.IntoIter.html -/
def PV_THR2_LibrarySemantics_IntoIterNext9 {W E : Type} (C : Carrier W Data)
    (values : Values W E) (fn : Data) (args : List Data)
    (s : Store Data) (w : W) : Option (Store Data) := do
  match args with
  | [reference] =>
    let (p,value) ← receiver C s w reference
    let ptr ← C.field value 4
    let finish ← C.field value 5
    let raw ← values.rawNonNull ptr
    if raw = finish then pure s
    else if values.width fn = 0 then
      let finish' ← values.subPointer finish 1
      writeAddress C s (withField p 5) (some finish')
    else
      let ptr' ← values.addNonNull ptr (values.width fn)
      writeAddress C s (withField p 4) (some ptr')
  | _ => none

/-- f167: alloc/src/vec/mod.rs push -> push_mut (session15 pinned bodies).
Reserve/grow_one supplies only the resulting RawVec value. This interpreter
performs both source header writes, buf then len; native element bytes stay
in OWNER memory. No final source Store is supplied by reserve.
https://doc.rust-lang.org/std/vec/struct.Vec.html#method.push -/
def PV_THR2_LibrarySemantics_VecPush167 {W E : Type} (C : Carrier W Data)
    (values : Values W E) (fn : Data) (args : List Data)
    (s : Store Data) (w : W) (r : Reply W E Data) : Option (Store Data) :=
  match r.answer with
  | .returned (.ok _) => do
    match args with
    | [reference,_] =>
      let (p,value) ← receiver C s w reference
      let buf ← C.field value 0
      let .number len ← C.field value 1 | none
      let buf' ← values.reserve fn buf len 1 w r
      let changed ← writeAddress C s (withField p 0) (some buf')
      writeAddress C changed (withField p 1) (some (.number (len+1)))
    | _ => none

  | _ => some s

/-- f10: alloc/src/vec/mod.rs append -> append_elements (session15 hashes).
Reserve destination, increase its length by the old other length, then set
other.len=0. Heap copies/allocator effects remain in r.world/r.events. These
are source-selected reference addresses, never a supplied alias. Rust's two
mutable references must be valid/disjoint at their caller, as usual.
https://doc.rust-lang.org/std/vec/struct.Vec.html#method.append -/
def PV_THR2_LibrarySemantics_VecAppend10 {W E : Type} (C : Carrier W Data)
    (values : Values W E) (fn : Data) (args : List Data)
    (s : Store Data) (w : W) (r : Reply W E Data) : Option (Store Data) :=
  match r.answer with
  | .returned (.ok _) => do
    match args with
    | [reference,other] =>
      let (p,value) ← receiver C s w reference
      let (q,source) ← receiver C s w other
      let buf ← C.field value 0
      let .number len ← C.field value 1 | none
      let .number count ← C.field source 1 | none
      let buf' ← values.reserve fn buf len count w r
      let changed ← writeAddress C s (withField p 0) (some buf')
      let changed ← writeAddress C changed (withField p 1) (some (.number (len+count)))
      writeAddress C changed (withField q 1) (some (.number 0))
    | _ => none

  | _ => some s

/-- The five-entry table is executable Store semantics, not an arbitrary
delta. Malformed source references/layouts return none and must not be called
adequate source instances. No identity delta is selected for a valid writer.
Reply status is independent: every answer is still delivered by the native
rule; this is a Store projection, not a new success-only machine. -/
def interpret {W E : Type} (C : Carrier W Data) (values : Values W E)
    (f : Function) (fn : Data) (args : List Data) (s : Store Data)
    (w : W) (r : Reply W E Data) : Option (Store Data) :=
  match f with
  | .cellReplace289 => PV_THR2_LibrarySemantics_CellReplace289 C args s w
  | .rangeNext93 => PV_THR2_LibrarySemantics_RangeNext93 C args s w
  | .intoIterNext9 => PV_THR2_LibrarySemantics_IntoIterNext9 C values fn args s w
  | .vecPush167 => PV_THR2_LibrarySemantics_VecPush167 C values fn args s w r
  | .vecAppend10 => PV_THR2_LibrarySemantics_VecAppend10 C values fn args s w r

/-- The concrete f289 meaning performs the root write for EVERY full reply,
including pending/failure/divergence. No desired-write premise is used. -/
theorem replace_root {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference value : Data) (p : Address)
    (address : C.dereference w reference = some {p with fields := []}) :
    PV_THR2_LibrarySemantics_CellReplace289 C [reference,value] s w =
      some (write s {p with fields := []} (some value)) := by
  change (C.dereference w reference).bind (fun q => writeAddress C s q (some value)) = _
  rw [address]
  rfl

theorem replace_written {W : Type} (C : Carrier W Data) (s : Store Data) (w : W)
    (reference value : Data) (p : Address)
    (address : C.dereference w reference = some {p with fields := []}) :
    ∃ changed, PV_THR2_LibrarySemantics_CellReplace289 C [reference,value] s w =
      some changed ∧ changed.cells {p with fields := []} = some value :=
  ⟨_,replace_root C s w reference value p address,write_same _ _ _⟩

#print axioms PV_THR2_LibrarySemantics_CellReplace289
#print axioms PV_THR2_LibrarySemantics_RangeNext93
#print axioms PV_THR2_LibrarySemantics_IntoIterNext9
#print axioms PV_THR2_LibrarySemantics_VecPush167
#print axioms PV_THR2_LibrarySemantics_VecAppend10
#print axioms interpret
#print axioms replace_root
#print axioms replace_written
end PV_THR2_SourceStoreLibrary
