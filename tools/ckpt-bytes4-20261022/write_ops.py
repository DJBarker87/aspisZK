from pathlib import Path
p=Path('docs/research/100bit-spend-path-20261013/lean/CheckpointBytes4Ops.lean')
s='''import CheckpointBytes4Weights
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
'''
for i in range(10):
 s+=f'  withK read '+('⟨bytes,start⟩' if i==0 else f'r{i}')+f' fun x{i} r{i+1} =>\n'
s+='  ok (.Ok (Array.make 10#usize ['+','.join(f'x{i}' for i in range(10))+'],r10.at))\n'
s+='''
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
'''
for i in range(22):
 s+=f'  let (b{i},r{i+1}) ← CheckpointBytes3Reader.raw 4#usize '+('⟨bytes,start⟩' if i==0 else f'r{i}')+'\n'
 s+=f'  let q{i} ← lift (core.num.U32.from_le_bytes b{i})\n'
s+='  ok (Array.make 22#usize ['+','.join(f'q{i}' for i in range(22))+'],r22.at)\n'
s+='''
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
'''
p.write_text(s)
