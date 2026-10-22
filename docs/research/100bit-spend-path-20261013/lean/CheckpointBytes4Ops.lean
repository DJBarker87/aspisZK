import CheckpointBytes4Weights
import CheckpointBytes3Allocation

/-! Concrete source-shaped callback content model. Allocation outcome remains
an execution parameter. Scalar from_le_bytes and helper implementation adoption
is the independent native operation boundary, not a kernel Rust extraction. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytes4Ops
open Aeneas Aeneas.Std Result
open AspisR1Stage2 CheckpointBytes4Sections

def listEq {T U : Type} (inst : core.cmp.PartialEq T U) : List T → List U → Result Bool
  | [], [] => ok true
  | x::xs, y::ys => do
      let same ← inst.eq x y
      if same then listEq inst xs ys else ok false
  | _, _ => ok false

def eq {T U : Type} {N : Usize} (inst : core.cmp.PartialEq T U)
    (s : Slice T) (a : Array U N) : Result Bool := listEq inst s.val a.val

def ne {T U : Type} {N : Usize} (inst : core.cmp.PartialEq T U)
    (s : Slice T) (a : Array U N) : Result Bool := do
  let same ← eq inst s a
  ok (!same)

def headerLoop : Nat → core.slice.iter.Iter U8 → Result (Bool × core.slice.iter.Iter U8)
  | 0, it => ok (false,it)
  | n+1, it => do
      let (value,rest) ← core.slice.iter.IteratorSliceIter.next it
      match value with
      | none => ok (false,rest)
      | some b => if b != 0#u8 then ok (true,rest) else headerLoop n rest

def headerAny (it : core.slice.iter.Iter U8) : Result (Bool × core.slice.iter.Iter U8) :=
  headerLoop (it.slice.val.length+1) it

def finalLen : transport.Variant → Result Usize
  | .S1 => ok 256#usize | .S2 => ok 64#usize | .D => ok 64#usize

def checkpointSize (v : transport.Variant) : Result Usize := do
  let n ← finalLen v
  let weights ← 16#usize * n
  744#usize + weights

def tag : transport.Variant → Result U8
  | .S1 => ok 1#u8 | .S2 => ok 2#u8 | .D => ok 3#u8

def zeroK : Result K := ok ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩

def queryLoop (seen : List U32) : List U32 → core.result.Result Unit verifier.Error
  | [] => .Ok ()
  | q::qs => if q.val ≥ 262144 ∨ q ∈ seen then .Err .Checkpoint
      else queryLoop (seen ++ [q]) qs

def validate (q : Array U32 22#usize) : Result (core.result.Result Unit verifier.Error) :=
  ok (queryLoop [] q.val)

def withK {T : Type} (read : ReadK) (r : verifier.Reader)
    (next : K → verifier.Reader → Result (core.result.Result T verifier.Error)) :
    Result (core.result.Result T verifier.Error) := do
  let (value,out) ← read r
  match value with
  | .Err e => ok (.Err e)
  | .Ok x => next x out

/-- The ten reads in the shipped helper, in their source order. -/
def semanticUsing (read : ReadK) (bytes : Slice U8) (start : Usize) :
    Result (core.result.Result (Array K 10#usize × Usize) verifier.Error) :=
  withK read ⟨bytes,start⟩ fun x0 r1 =>
  withK read r1 fun x1 r2 =>
  withK read r2 fun x2 r3 =>
  withK read r3 fun x3 r4 =>
  withK read r4 fun x4 r5 =>
  withK read r5 fun x5 r6 =>
  withK read r6 fun x6 r7 =>
  withK read r7 fun x7 r8 =>
  withK read r8 fun x8 r9 =>
  withK read r9 fun x9 r10 =>
  ok (.Ok (Array.make 10#usize [x0,x1,x2,x3,x4,x5,x6,x7,x8,x9],r10.at))

def readSemanticAlpha := semanticUsing CheckpointBytes3Reader.readK

/-- Source mutable next/back loop, over precisely the actual Vec length. -/
def weightsUsing (read : ReadK) (bytes : Slice U8) (start : Usize) (v : alloc.vec.Vec K) :
    Result (core.result.Result (alloc.vec.Vec K × Usize) verifier.Error) := do
  let result ← weightLoop read v.val.length ⟨bytes,start⟩ ⟨⟨v.val,v.property⟩,0⟩
  match result with
  | .Err e => ok (.Err e)
  | .Ok (it,r) => ok (.Ok (⟨it.slice.val,it.slice.property⟩,r.at))

def readWeights := weightsUsing CheckpointBytes3Reader.readK

/-- This legacy callback is unused by resumeWithOps, which emits all twenty-two
raw query reads directly. It still has a concrete ordered implementation. -/
def queryUsing (bytes : Slice U8) (start : Usize) :
    Result (Array U32 22#usize × Usize) := do
  let (b0,r1) ← CheckpointBytes3Reader.raw 4#usize ⟨bytes,start⟩
  let q0 ← lift (core.num.U32.from_le_bytes b0)
  let (b1,r2) ← CheckpointBytes3Reader.raw 4#usize r1
  let q1 ← lift (core.num.U32.from_le_bytes b1)
  let (b2,r3) ← CheckpointBytes3Reader.raw 4#usize r2
  let q2 ← lift (core.num.U32.from_le_bytes b2)
  let (b3,r4) ← CheckpointBytes3Reader.raw 4#usize r3
  let q3 ← lift (core.num.U32.from_le_bytes b3)
  let (b4,r5) ← CheckpointBytes3Reader.raw 4#usize r4
  let q4 ← lift (core.num.U32.from_le_bytes b4)
  let (b5,r6) ← CheckpointBytes3Reader.raw 4#usize r5
  let q5 ← lift (core.num.U32.from_le_bytes b5)
  let (b6,r7) ← CheckpointBytes3Reader.raw 4#usize r6
  let q6 ← lift (core.num.U32.from_le_bytes b6)
  let (b7,r8) ← CheckpointBytes3Reader.raw 4#usize r7
  let q7 ← lift (core.num.U32.from_le_bytes b7)
  let (b8,r9) ← CheckpointBytes3Reader.raw 4#usize r8
  let q8 ← lift (core.num.U32.from_le_bytes b8)
  let (b9,r10) ← CheckpointBytes3Reader.raw 4#usize r9
  let q9 ← lift (core.num.U32.from_le_bytes b9)
  let (b10,r11) ← CheckpointBytes3Reader.raw 4#usize r10
  let q10 ← lift (core.num.U32.from_le_bytes b10)
  let (b11,r12) ← CheckpointBytes3Reader.raw 4#usize r11
  let q11 ← lift (core.num.U32.from_le_bytes b11)
  let (b12,r13) ← CheckpointBytes3Reader.raw 4#usize r12
  let q12 ← lift (core.num.U32.from_le_bytes b12)
  let (b13,r14) ← CheckpointBytes3Reader.raw 4#usize r13
  let q13 ← lift (core.num.U32.from_le_bytes b13)
  let (b14,r15) ← CheckpointBytes3Reader.raw 4#usize r14
  let q14 ← lift (core.num.U32.from_le_bytes b14)
  let (b15,r16) ← CheckpointBytes3Reader.raw 4#usize r15
  let q15 ← lift (core.num.U32.from_le_bytes b15)
  let (b16,r17) ← CheckpointBytes3Reader.raw 4#usize r16
  let q16 ← lift (core.num.U32.from_le_bytes b16)
  let (b17,r18) ← CheckpointBytes3Reader.raw 4#usize r17
  let q17 ← lift (core.num.U32.from_le_bytes b17)
  let (b18,r19) ← CheckpointBytes3Reader.raw 4#usize r18
  let q18 ← lift (core.num.U32.from_le_bytes b18)
  let (b19,r20) ← CheckpointBytes3Reader.raw 4#usize r19
  let q19 ← lift (core.num.U32.from_le_bytes b19)
  let (b20,r21) ← CheckpointBytes3Reader.raw 4#usize r20
  let q20 ← lift (core.num.U32.from_le_bytes b20)
  let (b21,r22) ← CheckpointBytes3Reader.raw 4#usize r21
  let q21 ← lift (core.num.U32.from_le_bytes b21)
  ok (Array.make 22#usize [q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10,q11,q12,q13,q14,q15,q16,q17,q18,q19,q20,q21],r22.at)

def ops (reserved : Bool) : ResumeOps where
  checkpointSize := checkpointSize
  tag := tag
  finalLen := finalLen
  eq := eq
  ne := ne
  headerAny := headerAny
  raw := CheckpointBytes3Reader.raw
  readE := CheckpointBytes3Reader.readE
  readK := CheckpointBytes3Reader.readK
  validate := validate
  zeroK := zeroK
  filled := CheckpointBytes3Allocation.filled reserved
  readQueries := queryUsing
  readSemanticAlpha := readSemanticAlpha
  readWeights := readWeights

/-- Kernel C5 scalar identification through all ten reads, including Err. -/
theorem semantic_identification (bytes : Slice U8) (start : Usize) :
    readSemanticAlpha bytes start = semanticUsing c5ReadK bytes start := by
  have same : CheckpointBytes3Reader.readK = c5ReadK := funext read_k_identification
  unfold readSemanticAlpha
  rw [same]

/-- Kernel C5 scalar identification through every mutable weight read/write. -/
theorem weights_identification (bytes : Slice U8) (start : Usize) (v : alloc.vec.Vec K) :
    readWeights bytes start v = weightsUsing c5ReadK bytes start v := by
  have same : CheckpointBytes3Reader.readK = c5ReadK := funext read_k_identification
  unfold readWeights
  rw [same]

/-- The generic emitted-body theorem now consumes a closed callback record. -/
theorem successful_fields (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (bytes proof public1 : Slice U8)
    (v : transport.Variant) (hash : H) (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : verifier.resumeWithOps (ops reserved) D bytes proof public1 v hash =
      ok (.Ok (p,a))) :
    Nonempty (OraclePortCkptAbiSourceFields.Fields (ops reserved) bytes v p a) :=
  OraclePortCkptAbiSourceFields.successful_fields (ops reserved) D bytes proof public1 v hash p a success

/-- Successful execution derives allocation success; it does not assume it. -/
theorem successful_reservation (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (bytes proof public1 : Slice U8)
    (v : transport.Variant) (hash : H) (p : verifier.Prepared) (a : verifier.Accumulator)
    (success : verifier.resumeWithOps (ops reserved) D bytes proof public1 v hash =
      ok (.Ok (p,a))) : reserved = true := by
  obtain ⟨f⟩ := successful_fields reserved D bytes proof public1 v hash p a success
  exact (CheckpointBytes3Allocation.filled_success_content reserved f.finalLength f.zero
    f.allocated f.allocation).1

#print axioms semantic_identification
#print axioms weights_identification
#print axioms successful_fields
#print axioms successful_reservation
end AspisR1.CheckpointBytes4Ops
end
