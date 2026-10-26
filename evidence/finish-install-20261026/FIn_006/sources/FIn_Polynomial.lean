import FIn_Primitives
import SAG_EncodedField
import FIn_Horner
set_option autoImplicit false
noncomputable section
attribute [local irreducible] QuadraticAlgebra.instInv HAdd.hAdd HMul.hMul HPow.hPow CheckpointBytes5Output.ofE
namespace AspisR1.FIn_Polynomial
open Aeneas Aeneas.Std Result AspisR1Stage2.Stage2Finish
open scoped BigOperators

def mul (x y : E) : Result E := do
  let z ← AspisR1CurrentWide.field.wide_exact.WideExact.mul
    (SAQ_WideABI.toW x) (SAQ_WideABI.toW y)
  ok (SAQ_WideABI.fromW z)

def zero : E := ⟨⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩,⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩⟩

def go (bytes : Slice U8) (x : E) : List Usize → E → Result E
  | [], a => ok a
  | i::is, a => do
    let product ← mul a x
    let coefficient ← FIn_Primitives.field bytes i
    let next ← FIn_Primitives.add product coefficient
    go bytes x is next

/-- Seven source-ordered Horner updates, including the original ZERO multiply. -/
def polynomial (bytes : Slice U8) (x : E) : Result E :=
  go bytes x [6#usize,5#usize,4#usize,3#usize,2#usize,1#usize,0#usize] zero

theorem mul_value (x y z : E) (run : mul x y = ok z) :
    CheckpointBytes5Output.ofE z = CheckpointBytes5Output.ofE x * CheckpointBytes5Output.ofE y := by
  unfold mul at run
  obtain ⟨out,actual,rest⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := Result.ok.inj rest
  rw [←same,SAG_StageScale.from_decode,SAQ_WideABI.w_decode,SAQ_WideABI.w_decode]
  exact (SAQ_RawWide.mul_exact _ _ _ actual).2

theorem go_value (bytes : Slice U8) (x a out : E) (is : List Usize)
    (f : Nat → AspisWideTower.WideExact)
    (fields : ∀ i ∈ is, ∀ c, FIn_Primitives.field bytes i = ok c → CheckpointBytes5Output.ofE c = f i.val)
    (run : go bytes x is a = ok out) :
    CheckpointBytes5Output.ofE out =
      is.foldl (fun acc i => acc * CheckpointBytes5Output.ofE x + f i.val) (CheckpointBytes5Output.ofE a) := by
  induction is generalizing a with
  | nil => exact congrArg CheckpointBytes5Output.ofE (Result.ok.inj run.symm)
  | cons i is ih =>
    unfold go at run
    obtain ⟨product,hm,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨coefficient,hc,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    have tail := ih next (fun j hj => fields j (List.mem_cons_of_mem i hj)) run
    rw [tail,FIn_Primitives.add_value _ _ _ ha,mul_value _ _ _ hm,fields i (by simp) coefficient hc]
    rfl

theorem encoded_field (bytes : Slice U8) (f : Fin 7 → AspisWideTower.WideExact)
    (encoded : SelectedFieldSequenceCodec.encodeWide f = MultiproofConeCanonical.bytesOf bytes.val)
    (i : Usize) (c : E) (bound : i.val < 7)
    (run : FIn_Primitives.field bytes i = ok c) :
    CheckpointBytes5Output.ofE c = f ⟨i.val,bound⟩ := by
  unfold FIn_Primitives.field at run
  obtain ⟨out,actual,rest⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same := Result.ok.inj rest
  rw [←same,SAG_DotDecode.e_decode]
  change AspisR1CurrentWide.Proof.decodeFinish
    (SAG_DotAdapter.toFinishE (SAG_DotAdapter.toStageE out)) = _
  rw [SAG_DotAdapter.roundtrip_finishE]
  exact SAG_EncodedField.value bytes f encoded i out bound actual

theorem zero_value : CheckpointBytes5Output.ofE zero = 0 := by
  rfl

theorem value (bytes : Slice U8) (x out : E) (f : Fin 7 → AspisWideTower.WideExact)
    (encoded : SelectedFieldSequenceCodec.encodeWide f = MultiproofConeCanonical.bytesOf bytes.val)
    (run : polynomial bytes x = ok out) :
    CheckpointBytes5Output.ofE out = (OpeningPolynomialView.polynomial f).eval (CheckpointBytes5Output.ofE x) := by
  let coeff : Nat → AspisWideTower.WideExact := fun i => if h : i < 7 then f ⟨i,h⟩ else 0
  have h := go_value bytes x zero out _ coeff ?_ run
  · rw [zero_value] at h
    rw [OpeningPolynomialView.polynomial_eval]
    apply h.trans
    simpa only [List.foldl_cons,List.foldl_nil,coeff,
      show (6#usize).val = 6 from rfl, show (5#usize).val = 5 from rfl,
      show (4#usize).val = 4 from rfl, show (3#usize).val = 3 from rfl,
      show (2#usize).val = 2 from rfl, show (1#usize).val = 1 from rfl,
      show (0#usize).val = 0 from rfl, Nat.reduceLT, _root_.dite_true]
      using FIn_Horner.seven f (CheckpointBytes5Output.ofE x)
  · intro i hi c hc
    have bound : i.val < 7 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa only [coeff,dif_pos bound] using encoded_field bytes f encoded i c bound hc

#print axioms mul_value
#print axioms go_value
#print axioms encoded_field
#print axioms zero_value
#print axioms value
end AspisR1.FIn_Polynomial
end
