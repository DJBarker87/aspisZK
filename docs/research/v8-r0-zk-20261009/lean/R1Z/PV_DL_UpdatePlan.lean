import R1Z.PV_DL_BatchPlan
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_UpdatePlan
set_option autoImplicit false
/-- Byte-identical pure specification from V233's SplitObservation source.
Only its mathematical quotient/take/drop law is reused; its copy-dependent
Kani source-link credit is suspended under ruling (r). -/
def v233Specification (v : Slice U8) (size : Usize) : Result (List U8 × List U8) :=
  if size.val=0 then fail .divisionByZero else
    ok (v.val.take ((v.val.length/size.val)*size.val),
        v.val.drop ((v.val.length/size.val)*size.val))

theorem v233_native64 (input : Slice U8) :
    v233Specification input 64#usize=ok (PV_DL_BatchPlan.bulk input.val) := by
  unfold v233Specification
  rw [if_neg (by decide : (64#usize).val≠0)]
  rfl

structure Plan where
  buffer : List U8
  pos : Nat
  batches : List (List U8)

def write (buffer : List U8) (pos : Nat) (bytes : List U8) : List U8 :=
  buffer.take pos++bytes++buffer.drop (pos+bytes.length)

def first (buffer : List U8) (pos : Nat) (input : List U8) : List U8 :=
  if pos=0 then buffer else write buffer pos (input.take (64-pos))

def start (pos : Nat) : Nat := if pos=0 then 0 else 64-pos

def value (buffer : List U8) (pos : Nat) (input : List U8) : Plan :=
  if input.length<64-pos then ⟨write buffer pos input,pos+input.length,[]⟩ else
  let base := first buffer pos input
  let rest := input.drop (start pos)
  let split := PV_DL_BatchPlan.bulk rest
  ⟨write base 0 split.2,split.2.length,
    (if pos=0 then [] else [base])++PV_DL_BatchPlan.events rest⟩

/-- Owned Rust index formulation: preserve both native call boundaries and
all dead buffer bytes, including pos0 with an integral number of bulk blocks. -/
def reference (buffer : List U8) (pos : Nat) (input : List U8) : Plan :=
  let n := input.length
  let rem := 64-pos
  if n<rem then ⟨write buffer pos input,pos+n,[]⟩ else
  let begin := start pos
  let base := first buffer pos input
  let count := (n-begin)/64
  let ending := begin+count*64
  let payload := (input.drop begin).take (count*64)
  let tail := input.drop ending
  ⟨write base 0 tail,tail.length,
    (if pos=0 then [] else [base])++(if payload=[] then [] else [payload])⟩

theorem source_reference (buffer : List U8) (pos : Nat) (input : List U8) :
    reference buffer pos input=value buffer pos input := by
  unfold reference value
  by_cases h : input.length<64-pos
  · simp only [h,if_true]
  · simp only [h,if_false,PV_DL_BatchPlan.bulk,PV_DL_BatchPlan.events,List.length_drop]
    simp only [List.drop_drop,Nat.sub_sub]

theorem write_length (buffer bytes : List U8) (pos : Nat)
    (hb : buffer.length=64) (h : pos+bytes.length ≤ 64) :
    (write buffer pos bytes).length=64 := by
  simp only [write,List.length_append,List.length_take,List.length_drop,hb]
  omega

theorem first_length (buffer input : List U8) (pos : Nat)
    (hb : buffer.length=64) (hp : pos<64) (hn : 64-pos ≤ input.length) :
    (first buffer pos input).length=64 := by
  unfold first
  split
  · exact hb
  · apply write_length buffer _ pos hb
    simp only [List.length_take]
    omega

theorem shape (buffer input : List U8) (pos : Nat)
    (hb : buffer.length=64) (hp : pos<64) :
    (value buffer pos input).buffer.length=64 ∧ (value buffer pos input).pos<64 := by
  unfold value
  split
  · constructor
    · apply write_length buffer input pos hb;omega
    · change pos+input.length<64
      omega
  · have hf := first_length buffer input pos hb hp (by omega)
    have hr := PV_DL_BatchPlan.remainder (input.drop (start pos))
    constructor
    · apply write_length _ _ 0 hf
      omega
    · exact hr

/-- Compression is a batched callback. Whole bulk regions are never replaced
by a list of singleton calls, which is false for arbitrary callbacks. -/
def run {S : Type} (compress : S → List U8 → Result S) (state : S)
    (buffer : List U8) (pos : Nat) (input : List U8) : Result (S × List U8 × Nat) := do
  let plan := reference buffer pos input
  let state ← PV_DL_CompressionTrace.run compress plan.batches state
  ok (state,plan.buffer,plan.pos)

def model {S : Type} (compress : S → List U8 → Result S) (state : S)
    (buffer : List U8) (pos : Nat) (input : List U8) : Result (S × List U8 × Nat) := do
  let plan := value buffer pos input
  let state ← PV_DL_CompressionTrace.run compress plan.batches state
  ok (state,plan.buffer,plan.pos)

theorem complete {S : Type} (compress : S → List U8 → Result S) (state : S)
    (buffer : List U8) (pos : Nat) (input : List U8) :
    run compress state buffer pos input=model compress state buffer pos input := by
  unfold run model
  rw [source_reference]

#print axioms v233Specification
#print axioms v233_native64
#print axioms Plan
#print axioms write
#print axioms first
#print axioms start
#print axioms value
#print axioms reference
#print axioms source_reference
#print axioms write_length
#print axioms first_length
#print axioms shape
#print axioms run
#print axioms model
#print axioms complete
end R1Z.PV_DL_UpdatePlan
