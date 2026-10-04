import AspisV8R19.InverseRuntimeMul
import AspisV8R19.InverseChain

/-! Actual generated loop execution under the full cached Aeneas runtime.
Induction uses the remaining range length, never normalization of a large
concrete recurrence. -/
set_option autoImplicit false
namespace AspisV8R19.GeneratedInverseLoop
open Aeneas Aeneas.Std Result ControlFlow V7Tag73CurrentHelpersOpaque
open InverseChain

def encode (x : Word) : aspis_core.field.M31 :=
  UScalar.ofNatCore x.val (by have := x.isLt; change x.val < 2^32; unfold AspisV8R15.ExactTowerBase.P at *; omega)

@[simp] theorem encode_val (x : Word) : (encode x).val = x.val := rfl

theorem mul_encode (x y : Word) :
    aspis_core.field.M31.mul (encode x) (encode y) = .ok (encode (wordMul x y)) := by
  obtain ⟨z, hz, hv, _⟩ := InverseRuntimeMul.generated_mul_mod (encode x) (encode y)
  rw [hz]
  congr 1
  apply UScalar.eq_of_val_eq
  rw [hv, encode_val, encode_val, encode_val]
  change (x.val*y.val) % AspisV8R17.RawReducer.P =
    AspisV8R17.RawReducer.rawReduceU64 (x.val*y.val)
  symm
  apply AspisV8R17.RawReducer.rawReduceU64_eq_mod_nat
  have hx : x.val < 2^32 := (encode x).hBounds
  have hy : y.val < 2^32 := (encode y).hBounds
  have hp := Nat.mul_lt_mul_of_lt_of_lt hx hy
  exact hp

theorem range_next (r : core.ops.range.Range Usize) :
    core.iter.range.IteratorRange.next core.iter.range.StepUsize r =
    if h : r.start.val < r.end.val then
      .ok (some r.start, {start := (UScalar.ofNatCore (r.start.val+1)
        (by have := r.end.hBounds; omega)), «end» := r.end})
    else .ok (none, r) := by
  by_cases h : r.start.val < r.end.val
  · have hb : r.start.val + 1 ≤ UScalar.max .Usize := by
      rw [UScalar.max]
      have := r.end.hBounds
      omega
    have hb' : r.start.val < UScalar.max .Usize := by omega
    simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
      core.iter.range.UScalarStep, core.cmp.PartialOrdUsize,
      core.cmp.impls.PartialOrdUsize.lt, core.clone.CloneUsize,
      liftFun2, liftFun1, h, core.iter.range.UScalarStep.forward_checked, hb']
  · simp [core.iter.range.IteratorRange.next, core.iter.range.StepUsize,
      core.iter.range.UScalarStep, core.cmp.PartialOrdUsize,
      core.cmp.impls.PartialOrdUsize.lt, liftFun2, h]

theorem loop_exec (n : Nat) (r : core.ops.range.Range Usize) (x : Word)
    (hn : r.end.val-r.start.val = n) :
    aspis_core.field.square_n_loop r (encode x) =
      .ok (encode (squares wordMul n x)) := by
  induction n generalizing r x with
  | zero =>
      have h : ¬ r.start.val < r.end.val := by omega
      have hb : aspis_core.field.square_n_loop.body r (encode x) = .ok (.done (encode x)) := by
        simp only [aspis_core.field.square_n_loop.body, range_next, dif_neg h, bind_tc_ok]
      rw [aspis_core.field.square_n_loop, loop.eq_def]
      simp only [hb, squares]
  | succ n ih =>
      have h : r.start.val < r.end.val := by omega
      let r' : core.ops.range.Range Usize :=
        {start := UScalar.ofNatCore (r.start.val+1)
          (by have := r.end.hBounds; omega), «end» := r.end}
      have hn' : r'.end.val-r'.start.val = n := by
        change r.end.val-(r.start.val+1) = n
        omega
      have hb : aspis_core.field.square_n_loop.body r (encode x) =
          .ok (.cont (r', encode (wordMul x x))) := by
        simp only [aspis_core.field.square_n_loop.body, range_next, dif_pos h,
          bind_tc_ok, mul_encode, r']
      rw [aspis_core.field.square_n_loop, loop.eq_def]
      simp only [hb]
      exact ih r' (wordMul x x) hn'

theorem square_n_exec (x : Word) (count : Usize) :
    aspis_core.field.square_n (encode x) count =
      .ok (encode (squares wordMul count.val x)) := by
  apply loop_exec
  simp

theorem inv_zero (x : Word) (hx : x.val = 0) :
    aspis_core.field.M31.inv (encode x) = .fail .assertionFailure := by
  have he : encode x = 0#u32 := UScalar.eq_of_val_eq (by simpa using hx)
  simp [aspis_core.field.M31.inv, he, massert]

theorem inv_nonzero (x : Word) (hx : x.val ≠ 0) :
    aspis_core.field.M31.inv (encode x) = .ok (encode (wordChain x)) := by
  have he : encode x ≠ 0#u32 := UScalar.ne_of_val_ne (by simpa using hx)
  simp [aspis_core.field.M31.inv, he, massert, mul_encode, square_n_exec,
    wordChain, chain]

theorem inv_refines_guarded (x : Word) :
    aspis_core.field.M31.inv (encode x) =
      match guarded x with
      | .error _ => .fail .assertionFailure
      | .ok y => .ok (encode y) := by
  by_cases h : x.val = 0
  · rw [zero_rejected x h, inv_zero x h]
  · rw [(nonzero_success x h).1, inv_nonzero x h]

theorem inv_correct (self : aspis_core.field.M31)
    (hc : self.val < AspisV8R15.ExactTowerBase.P) (hne : self.val ≠ 0) :
    ∃ out : aspis_core.field.M31,
      aspis_core.field.M31.inv self = .ok out ∧
      out.val < AspisV8R15.ExactTowerBase.P ∧
      (out.val : AspisV8R15.ExactTowerBase.M31Exact) =
        (self.val : AspisV8R15.ExactTowerBase.M31Exact)⁻¹ := by
  let x : Word := ⟨self.val, hc⟩
  have he : encode x = self := UScalar.eq_of_val_eq rfl
  refine ⟨encode (wordChain x), ?_, (wordChain x).isLt, ?_⟩
  · rw [← he]; exact inv_nonzero x hne
  · exact wordChain_inverse x hne

#print axioms encode_val
#print axioms mul_encode
#print axioms range_next
#print axioms loop_exec
#print axioms square_n_exec
#print axioms inv_zero
#print axioms inv_nonzero
#print axioms inv_refines_guarded
#print axioms inv_correct
end AspisV8R19.GeneratedInverseLoop
