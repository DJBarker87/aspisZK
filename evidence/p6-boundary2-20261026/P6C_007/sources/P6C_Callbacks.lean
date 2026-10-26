import P6C_Extension
import Port9OR_P6Node
import Port4B_LeafCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.P6C_Callbacks
open Aeneas Aeneas.Std Result SdkC_Source
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

/-- Exact source digest compression: one syscall, one returned value and no
extra calls. Applies to binary, occupied and supplied-sibling inputs alike. -/
theorem digest (hashv : Parts → Result Digest) (sha256 H : Bytes → State)
    (p1 : S2W_ExtractionBoundary.P1 sha256 H)
    (syscall : S2W_ExtractionBoundary.RuntimeSyscall hashv sha256)
    (parts : Parts) (value : Digest) (before : Log)
    (accepted : hashv parts = ok value) :
    value = MultiproofConePhysicalTransport.rawOracle H parts ∧
    run hashv (digestCode parts) before =
      (ok value,before ++ [⟨parts,ok value⟩]) := by
  have same := (P6C_Extension.agrees hashv H parts value accepted).symm.trans
    (P6C_Extension.realization hashv sha256 H p1 syscall parts)
  exact ⟨same,by rw [digest_trace,accepted]⟩

/-- Includes the source's post-compression checked scratch writes. The failed
mutation case retains the issued digest attempt instead of inventing a suffix. -/
theorem parent_trace (hashv : Parts → Result Digest)
    (s : MultiproofConeRef.reference.Scratch) (left right : Digest)
    (ni cursor : Usize) (index : U32) (w : Usize) (before : Log) :
    run hashv (Port9OR_P6Node.parent s left right ni cursor index w) before =
      (match hashv (MultiproofConePhysicalDigest.parts left right) with
       | .ok value => MultiproofConePhysicalProgram.finish s value ni cursor index w
       | .fail e => .fail e
       | .div => .div,
       before ++ [⟨MultiproofConePhysicalDigest.parts left right,
         hashv (MultiproofConePhysicalDigest.parts left right)⟩]) := by
  cases actual : hashv (MultiproofConePhysicalDigest.parts left right) with
  | fail e => simp only [Port9OR_P6Node.parent,run,actual]
  | div => simp only [Port9OR_P6Node.parent,run,actual]
  | ok value =>
    simp only [Port9OR_P6Node.parent,run,actual,CheckpointBytes5Effect.liftResult]
    cases MultiproofConePhysicalProgram.finish s value ni cursor index w <;> rfl

/-- All returning parent bodies have exactly one successful compression
attempt, including its actual argument carrier and the resulting scratch. -/
theorem parent_accepted (hashv : Parts → Result Digest)
    (s : MultiproofConeRef.reference.Scratch) (left right : Digest)
    (ni cursor : Usize) (index : U32) (w : Usize) (before : Log)
    (out : MultiproofConeRef.reference.Row)
    (accepted : (run hashv (Port9OR_P6Node.parent s left right ni cursor index w) before).1 = ok out) :
    ∃ value, hashv (MultiproofConePhysicalDigest.parts left right) = ok value ∧
      MultiproofConePhysicalProgram.finish s value ni cursor index w = ok out ∧
      run hashv (Port9OR_P6Node.parent s left right ni cursor index w) before =
        (ok out,before ++ [⟨MultiproofConePhysicalDigest.parts left right,ok value⟩]) := by
  rw [parent_trace] at accepted ⊢
  cases actual : hashv (MultiproofConePhysicalDigest.parts left right) with
  | fail e => simp only [actual] at accepted; cases accepted
  | div => simp only [actual] at accepted; cases accepted
  | ok value =>
    simp only [actual] at accepted ⊢
    exact ⟨value,rfl,accepted,congrArg (fun result => (result,_)) accepted⟩

/-- Literal installed leaf body, with its fixed physical opening width. All
kind values and all opening bytes are quantified; no honest-leaf restriction. -/
theorem leaf_trace (hashv : Parts → Result Digest) (kind : Usize)
    (o : Slice U8) (width : o.val.length = 832) (before : Log) :
    run hashv (Port4B_LeafCode.code kind o) before =
      (hashv (Port4B_LeafCode.input kind o),
        before ++ [⟨Port4B_LeafCode.input kind o,hashv (Port4B_LeafCode.input kind o)⟩]) := by
  have range (s e : Usize) (order : s.val ≤ e.val) (fit : e.val ≤ 832) :
      Port4B_LeafCode.readRange o s e = ok (MultiproofConeSlices.sub o s e) :=
    MultiproofConeSlices.range_total o s e order (by omega)
  unfold Port4B_LeafCode.code Port4B_LeafCode.input
  split <;> (try split)
  all_goals simp only [Port4B_LeafCode.codeFor,run,
    range 608#usize 640#usize (by decide) (by decide),
    range 0#usize 480#usize (by decide) (by decide),
    range 640#usize 672#usize (by decide) (by decide),
    range 480#usize 608#usize (by decide) (by decide),
    range 800#usize 832#usize (by decide) (by decide),
    range 672#usize 800#usize (by decide) (by decide)]
  all_goals split <;> rfl

#print axioms digest
#print axioms parent_trace
#print axioms parent_accepted
#print axioms leaf_trace
end AspisR1.P6C_Callbacks
end
