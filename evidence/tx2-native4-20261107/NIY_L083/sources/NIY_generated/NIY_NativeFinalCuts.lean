import NIY_NativeCuts
import NIL_StatePort
set_option autoImplicit false
noncomputable section
namespace NIY_NativeFinalCuts
open Aeneas Aeneas.Std NIL_Carriers NIY_NativeCuts

structure Descriptor where
 address : Nat
 length : Nat
 capacity : Nat

structure Returned where
 boxAddress : Nat
 prepared : NIL_StatePort.F.P
 accumulator : NIL_StatePort.F.A
 descriptor : Descriptor

def wordOf (v : alloc.vec.Vec Fresh.K) (i j : Nat) : Nat :=
 ((v.val[i]?).map (fun k=>limbK k j)).getD 0

/-- NIY_ctor_payload.rs.txt SHA256 36bfc7a07aebb01cd25645fddc795ae1b7ac33a9200b6db1cf66fd7ff6404459. The harness constructs variant S2,
length64/capacity64 with all64 K cells arbitrary. This precondition is explicit;
its actual caller/producer installation remains an OPEN obligation. -/
def windowPre (p : NIL_StatePort.F.P) (a : NIL_StatePort.F.A) (d : Descriptor) : Prop :=
 p.variant=.S2 ∧ a.weights.val.length=64 ∧ d.length=64 ∧ d.capacity=64

/-- NIY_ctor_payload.rs.txt SHA256 36bfc7a07aebb01cd25645fddc795ae1b7ac33a9200b6db1cf66fd7ff6404459. Positive assertions:
"assert_eq!(out.as_ref() as *const Prepared as usize,allocation);"
"assert_eq!(after.next,next_byte as usize);"
"assert_eq!(after.weights.as_ptr() as usize,pointer);"
"assert_eq!(after.weights.len(),64);assert_eq!(after.weights.capacity(),capacity);"
"assert_eq!(kw(after.weights[wi],j),selected);"
The Err arm asserts matches!(result,Err(Error::Checkpoint)) and allocation=0.
NO Prepared-field equality is added: that timed-out conjunct stays excluded. -/
def windowCut (before : NIL_StatePort.F.A) (d : Descriptor)
 (end1 at2 : Usize) (next : U8) (allocated : Nat) (i : Fin 64) (j : Fin 4)
 (result : core.result.Result Returned Fresh.Err) : Prop :=
 match result with
 | .Err err => at2≠end1 ∧ err=.Checkpoint ∧ allocated=0
 | .Ok out => at2=end1 ∧ out.boxAddress=allocated ∧
     out.accumulator.next.val=next.val ∧ out.descriptor.address=d.address ∧
     out.descriptor.length=64 ∧ out.descriptor.capacity=d.capacity ∧
     out.accumulator.weights.val.length=64 ∧
     wordOf out.accumulator.weights i.val j.val=wordOf before.weights i.val j.val

/-- NIY_weight_frame.rs.txt SHA256 2b69d2a9a7f2431c26b0cb94c00c3bd08a19b0e37a8e3581ba58b02004b433fa. "assert_eq!(v.len(),0);"
"match reply{Ok(())=>assert_eq!(v.capacity(),64^(if cfg!(NIY_invert){1}else{0})),Err(_)=>assert_eq!(v.capacity(),0)}".
Positive configuration NIY_invert=false. No allocation availability is assumed. -/
def reserveCut (success : Bool) (length capacity : Nat) : Prop :=
 length=0 ∧ if success then capacity=64 else capacity=0

/-- NIY_weight_frame.rs.txt SHA256 2b69d2a9a7f2431c26b0cb94c00c3bd08a19b0e37a8e3581ba58b02004b433fa. Assumed native prestate:
bytes1768, all64 initialized K cells arbitrary, i/observed<64 and j<4;
at=712+16*i. Capacity64 is exposed rather than silently generalized. -/
def weightPre (bytes : Slice U8) (v : alloc.vec.Vec Fresh.K) (d : Descriptor)
 (i : Fin 64) (cursor : Usize) : Prop :=
 bytes.val.length=1768 ∧ v.val.length=64 ∧ d.length=64 ∧ d.capacity=64 ∧
 cursor.val=712+16*i.val

/-- NIY_weight_frame.rs.txt SHA256 2b69d2a9a7f2431c26b0cb94c00c3bd08a19b0e37a8e3581ba58b02004b433fa. "assert_eq!(it.len(),63-i);"
"assert_eq!(weights.as_ptr(),pointer);assert_eq!(weights.len(),64);assert_eq!(weights.capacity(),capacity);assert_eq!(reader.at,at+16);"
"match reply{Ok(value)=>assert_eq!(kw(weights[observed],j),if observed==i{kw(value,j)}else{before}),Err(error)=>{assert_eq!(error,Error::Checkpoint);assert_eq!(kw(weights[observed],j),before);}}".
This is the cut BEFORE rejection propagation/Drop, not a returning Err Vec.
The universally selected cell/limb refer to the SAME before/after vectors. -/
def weightCut (before after : alloc.vec.Vec Fresh.K) (d out : Descriptor)
 (i : Fin 64) (remaining : Nat) (cursor : Usize)
 (reply : core.result.Result Fresh.K Fresh.Err) : Prop :=
 out.address=d.address ∧ out.length=64 ∧ out.capacity=d.capacity ∧
 after.val.length=64 ∧ remaining=63-i.val ∧ cursor.val=712+16*i.val+16 ∧
 match reply with
 | .Ok value => ∀ observed : Fin 64,∀ j : Fin 4,
     wordOf after observed.val j.val=
       if observed.val=i.val then limbK value j.val else wordOf before observed.val j.val
 | .Err err => err=.Checkpoint ∧ ∀ observed : Fin 64,∀ j : Fin 4,
     wordOf after observed.val j.val=wordOf before observed.val j.val

#print axioms windowPre
#print axioms windowCut
#print axioms reserveCut
#print axioms weightPre
#print axioms weightCut
end NIY_NativeFinalCuts
