import Lean
import NFN_PhaseTransport
import NFN_ReserveOwner
import FIo_ReduceBounds
import NFN_GeometryPart01
import LPe_MersenneReduction
import SAQ_SquareSourceModel
import SAQ_Inverse
import NEF_FrozenInvRef.Funs
import NEW_InverseActual.Funs
import NDH_Geometry
import NEA_PointParam.Funs
import R17FibrePointActualSuccess
import NEA_TableCanonical

-- BEGIN copied LPf_ReductionWord: lean/LPf_ReductionWord.lean
set_option autoImplicit false
namespace AspisR1.NFN_LPf_ReductionWord
open Aeneas Aeneas.Std Result

/-- The native word fold has the natural value used in LPe's reduction theorem. -/
theorem fold_value (x : U64) :
    (FIo_ReduceBounds.fold x).val = LPe_MersenneReduction.fold x.val :=
by
  unfold FIo_ReduceBounds.fold U64.wrapping_add
  rw [UScalar.wrapping_add_val_eq, Nat.mod_eq_of_lt (FIo_ReduceBounds.sum_bound x)]
  have low : (x &&& 2147483647#u64).val = x.val % 2147483648 := by
    change (x.bv &&& (2147483647 : BitVec 64)).toNat = x.val % 2147483648
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.val 31
  rw [low, FIo_ReduceBounds.shr_val]
  rfl

theorem twice_value (x : U64) :
    (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)).val =
      LPe_MersenneReduction.fold (LPe_MersenneReduction.fold x.val) := by
  rw [fold_value, fold_value]

/-- Exact value of the actual extracted private reducer, including word casts
and wrapping subtraction. No successful output observation is a premise. -/
theorem native_reduce (x : U64) : ∃ z,
    FIo_Native.fast_pairing.canonical.reduce x = ok z ∧
    z.val = x.val % 2147483647 ∧ z.val < 2147483647 := by
  have hx : x.val < 18446744073709551616 := by scalar_tac
  have small : (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)).val < 4294967294 := by
    rw [twice_value]
    exact LPe_MersenneReduction.fold_twice_lt x.val hx
  have value := twice_value x
  have residue := LPe_MersenneReduction.reduce_eq_mod x.val hx
  unfold FIo_Native.fast_pairing.canonical.reduce
  simp only [FIo_Native.fast_pairing.canonical.P, lift, bind_tc_ok]
  change ∃ z, (if FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x) ≥ 2147483647#u64
    then ok (UScalar.cast .U32 (U64.wrapping_sub
      (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)) 2147483647#u64))
    else ok (UScalar.cast .U32 (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)))) = ok z ∧ _
  split
  · rename_i h
    have lower : 2147483647 ≤ (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)).val := by scalar_tac
    refine ⟨_, rfl, ?_, ?_⟩
    · unfold U64.wrapping_sub
      rw [UScalar.cast_val_eq, UScalar.wrapping_sub_val_eq]
      norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits,U32.size,U32.numBits]
      unfold LPe_MersenneReduction.reduce at residue
      rw [if_pos (by omega)] at residue
      omega
    · unfold U64.wrapping_sub
      rw [UScalar.cast_val_eq, UScalar.wrapping_sub_val_eq]
      norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits,U32.size,U32.numBits]
      omega
  · rename_i h
    have lower : (FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)).val < 2147483647 := by scalar_tac
    refine ⟨_, rfl, ?_, ?_⟩
    · rw [UScalar.cast_val_eq]
      norm_num [UScalar.size,UScalarTy.numBits,U32.size,U32.numBits]
      unfold LPe_MersenneReduction.reduce at residue
      rw [if_neg (by omega)] at residue
      omega
    · scalar_tac

#print axioms fold_value
#print axioms twice_value
#print axioms native_reduce
end AspisR1.NFN_LPf_ReductionWord
-- END copied LPf_ReductionWord
-- BEGIN copied LPf_CoreReduction: lean/LPf_CoreReduction.lean
set_option autoImplicit false
namespace AspisR1.NFN_LPf_CoreReduction
open Aeneas Aeneas.Std Result

/-- The two frozen source reducers place the u32 cast on opposite sides of
subtraction. Their twice-folded bounds make those placements equivalent. -/
theorem same (x : U64) :
    FIo_Native.aspis_core.field.reduce_u64 x =
    FIo_Native.fast_pairing.canonical.reduce x := by
  let m := FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)
  have small : m.val < 4294967294 := by
    rw [NFN_LPf_ReductionWord.twice_value]
    apply LPe_MersenneReduction.fold_twice_lt
    scalar_tac
  have cv : (UScalar.cast .U32 m).val = m.val := by scalar_tac
  unfold FIo_Native.aspis_core.field.reduce_u64 FIo_Native.fast_pairing.canonical.reduce
  simp only [FIo_Native.aspis_core.field.P, FIo_Native.fast_pairing.canonical.P,
    lift, bind_tc_ok]
  change (if UScalar.cast .U32 m ≥ 2147483647#u32
    then ok (U32.wrapping_sub (UScalar.cast .U32 m) 2147483647#u32)
    else ok (UScalar.cast .U32 m)) =
    (if m ≥ 2147483647#u64
    then ok (UScalar.cast .U32 (U64.wrapping_sub m 2147483647#u64))
    else ok (UScalar.cast .U32 m))
  split
  · rename_i h
    have hm : m ≥ 2147483647#u64 := by scalar_tac
    rw [if_pos hm]
    congr 1
    apply UScalar.eq_of_val_eq
    unfold U32.wrapping_sub U64.wrapping_sub
    rw [UScalar.cast_val_eq, UScalar.wrapping_sub_val_eq,
      UScalar.wrapping_sub_val_eq]
    norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits,U32.size,U32.numBits]
    omega
  · rename_i h
    have hm : ¬m ≥ 2147483647#u64 := by scalar_tac
    rw [if_neg hm]

/-- Total exact base-field reduction on every source word. -/
theorem source (x : U64) : ∃ z,
    FIo_Native.aspis_core.field.reduce_u64 x = ok z ∧
    z.val = x.val % 2147483647 ∧ z.val < 2147483647 := by
  rw [same]
  exact NFN_LPf_ReductionWord.native_reduce x

#print axioms same
#print axioms source
end AspisR1.NFN_LPf_CoreReduction
-- END copied LPf_CoreReduction
-- BEGIN copied LPf_BaseMultiply: lean/LPf_BaseMultiply.lean
set_option autoImplicit false
namespace AspisR1.NFN_LPf_BaseMultiply
open Aeneas Aeneas.Std Result

/-- Full u32 operands, without a canonical-input restriction. -/
theorem product_bound (x y : U32) : x.val * y.val < 18446744073709551616 := by
  have hx : x.val ≤ 4294967295 := by scalar_tac
  have hy : y.val ≤ 4294967295 := by scalar_tac
  have bound := Nat.mul_le_mul hx hy
  omega

theorem word_product (x y : U32) :
    (U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y)).val = x.val*y.val := by
  rw [U64.wrapping_mul_val_eq]
  have cx : (UScalar.cast .U64 x).val = x.val := by scalar_tac
  have cy : (UScalar.cast .U64 y).val = y.val := by scalar_tac
  rw [cx, cy]
  apply Nat.mod_eq_of_lt
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]
  exact product_bound x y

/-- The actual extracted frozen M31 multiplication is total and equals
natural multiplication modulo P. This is a Lean source theorem, not a claim
that the timed-out Kani exact contract passed. -/
theorem source (x y : U32) : ∃ z,
    FIo_Native.aspis_core.field.M31.mul x y = ok z ∧
    z.val = (x.val*y.val) % 2147483647 ∧ z.val < 2147483647 := by
  obtain ⟨z, run, val, canonical⟩ := NFN_LPf_CoreReduction.source
    (U64.wrapping_mul (UScalar.cast .U64 x) (UScalar.cast .U64 y))
  refine ⟨z, ?_, ?_, canonical⟩
  · simp only [FIo_Native.aspis_core.field.M31.mul,lift,bind_tc_ok,run]
  · rw [word_product] at val
    exact val

#print axioms product_bound
#print axioms word_product
#print axioms source
end AspisR1.NFN_LPf_BaseMultiply
-- END copied LPf_BaseMultiply
-- BEGIN copied NBG_SquareLoop: lean/NBG_SquareLoop.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NBG_SquareLoop
open Aeneas Aeneas.Std Result AspisR1
open AspisR1M31Inverse.SquareProof

theorem mul_total : TotalMul FIo_Native.aspis_core.field.M31.mul := by
  intro x y
  obtain ⟨z,run,_,_⟩ := NFN_LPf_BaseMultiply.source x y
  exact ⟨z,run⟩

theorem mul_refines : RefinesMul FIo_Native.aspis_core.field.M31.mul := by
  intro x y z run
  obtain ⟨out,call,value,_⟩ := NFN_LPf_BaseMultiply.source x y
  have same : out = z := Result.ok.inj (call.symm.trans run)
  subst out
  change (z.val : ZMod 2147483647) = (x.val : ZMod 2147483647) * (y.val : ZMod 2147483647)
  rw [value]
  simp

/-- Reuses the existing symbolic range induction. Every raw32-bit initial
value and every machine count are allowed; no successful return is assumed. -/
theorem square_n_result (value : U32) (count : Usize) :
    ∃ out, AspisR1M31Inverse.field.square_n
        FIo_Native.aspis_core.field.M31.mul value count = ok out ∧
      R17CurrentM31Semantics.decode out =
        R17CurrentM31Semantics.decode value ^ (2 ^ count.val) :=
  square_n_total_model _ mul_total mul_refines value count

#print axioms mul_total
#print axioms mul_refines
#print axioms square_n_result
#print axioms AspisR1.NFN_LPf_BaseMultiply.source
end NFN_NBG_SquareLoop
-- END copied NBG_SquareLoop
-- BEGIN copied NBG_InverseBridge: lean/NBG_InverseBridge.lean
set_option autoImplicit false
noncomputable section
namespace NFN_NBG_InverseBridge
open Aeneas Aeneas.Std Result AspisR1

theorem mul_eq_probe (x y : U32) :
    FIo_Native.aspis_core.field.M31.mul x y =
      AspisR1Qm31ArithmeticProbe.field.M31.mul x y := by
  obtain ⟨a,ha,va,_⟩ := NFN_LPf_BaseMultiply.source x y
  obtain ⟨b,hb,vb,_⟩ := ExtractedCurrentReducer.current_mul_mod x y
  have same : a = b := UScalar.eq_of_val_eq (va.trans vb.symm)
  rw [ha,hb,same]

/-- Full raw-word Result, including the zero assertion and noncanonical
representations. No nonzero or successful-return premise is supplied. -/
theorem inverse_result (x : U32) :
    AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul x =
      Port4C_InverseExecution.inverse_owned x := by
  have same : FIo_Native.aspis_core.field.M31.mul =
      AspisR1Qm31ArithmeticProbe.field.M31.mul := funext (fun a => funext (mul_eq_probe a))
  rw [same]
  change SAQ_Inverse.source x = Port4C_InverseExecution.inverse_owned x
  exact congrFun SAQ_Inverse.source_eq_reference x

#print axioms mul_eq_probe
#print axioms inverse_result
end NFN_NBG_InverseBridge
-- END copied NBG_InverseBridge
-- BEGIN copied NET_MultiplyBridge: evidence/slice-q-compose3-20261102/NET_MultiplyBridge.lean
set_option autoImplicit false
namespace NFN_NET_MultiplyBridge
open Aeneas Aeneas.Std Result AspisR1

/-- The independently emitted checked reducer equals the coherent release
reducer on every raw U64. Its folds fit; no concrete large reduction is run. -/
theorem reducer (x : U64) :
 NEF_FrozenInvRef.field.reduce_u64 x = FIo_Native.aspis_core.field.reduce_u64 x := by
 let m := FIo_ReduceBounds.fold (FIo_ReduceBounds.fold x)
 have small : m.val < 4294967294 := by
  rw [NFN_LPf_ReductionWord.twice_value]
  apply LPe_MersenneReduction.fold_twice_lt
  scalar_tac
 have mask : UScalar.cast .U64 (2147483647#u32) = 2147483647#u64 := by scalar_tac
 unfold NEF_FrozenInvRef.field.reduce_u64 FIo_Native.aspis_core.field.reduce_u64
 simp only [NEF_FrozenInvRef.field.P,FIo_Native.aspis_core.field.P,lift,bind_tc_ok,
  mask,FIo_ReduceFacts.shr31]
 rw [FIo_ReduceBounds.checked x]
 simp only [bind_tc_ok]
 rw [FIo_ReduceBounds.checked (FIo_ReduceBounds.fold x)]
 simp only [bind_tc_ok]
 change (if UScalar.cast .U32 m >= 2147483647#u32
   then UScalar.cast .U32 m - 2147483647#u32 else ok (UScalar.cast .U32 m)) =
  (if UScalar.cast .U32 m >= 2147483647#u32
   then ok (U32.wrapping_sub (UScalar.cast .U32 m) 2147483647#u32) else ok (UScalar.cast .U32 m))
 split
 · apply FIo_ScalarBridge.sub
   scalar_tac
 · rfl

/-- Full raw U32 domain, including the actual checked product and Result. -/
theorem product (x y : U32) :
 NEF_FrozenInvRef.field.M31.mul x y = FIo_Native.aspis_core.field.M31.mul x y := by
 have bound : (UScalar.cast .U64 x).val * (UScalar.cast .U64 y).val < UScalar.size .U64 := by
  have h := NFN_LPf_BaseMultiply.product_bound x y
  have cx : (UScalar.cast .U64 x).val=x.val := by scalar_tac
  have cy : (UScalar.cast .U64 y).val=y.val := by scalar_tac
  rw [cx,cy]
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits]
  exact h
 have native := FIo_ScalarBridge.mul (UScalar.cast .U64 x) (UScalar.cast .U64 y) bound
 simp only [NEF_FrozenInvRef.field.M31.mul,FIo_Native.aspis_core.field.M31.mul,
  lift,bind_tc_ok,native,reducer]
 rfl

/-- Paired meaning for each of the four product replies in the adopted CM
seven-call log; the caller must still establish its other child domains. -/
theorem product_reply (x y : U32) : ∃ z,
 NEF_FrozenInvRef.field.M31.mul x y=ok z ∧
 z.val=(x.val*y.val)%2147483647 ∧ z.val<2147483647 := by
 rw [product]
 exact NFN_LPf_BaseMultiply.source x y

#print axioms reducer
#print axioms product
#print axioms product_reply
end NFN_NET_MultiplyBridge
-- END copied NET_MultiplyBridge
-- BEGIN copied NEW_InverseAssociation: evidence/slice-q-compose4-20261104/NEW_InverseAssociation.lean
set_option autoImplicit false
namespace NFN_NEW_InverseAssociation
open Aeneas Aeneas.Std Result ControlFlow AspisR1

/-- Literal frozen-source reducer: no additional arithmetic proof or input restriction. -/
theorem reducer (x : U64) :
    NEW_InverseActual.aspis_core.field.reduce_u64 x =
      FIo_Native.aspis_core.field.reduce_u64 x := by
  simp only [NEW_InverseActual.aspis_core.field.reduce_u64,
    FIo_Native.aspis_core.field.reduce_u64,
    NEW_InverseActual.aspis_core.field.P,FIo_Native.aspis_core.field.P]

theorem multiply (x y : U32) :
    NEW_InverseActual.aspis_core.field.M31.mul x y =
      FIo_Native.aspis_core.field.M31.mul x y := by
  simp only [NEW_InverseActual.aspis_core.field.M31.mul,
    FIo_Native.aspis_core.field.M31.mul,reducer]

/-- One actual native square-loop body, with the same iterator and field word. -/
theorem square_body (iter : core.ops.range.Range Usize) (x : U32) :
    NEW_InverseActual.aspis_core.field.square_n_loop.body iter x =
      AspisR1M31Inverse.field.square_n_loop.body
        FIo_Native.aspis_core.field.M31.mul iter x := by
  simp only [NEW_InverseActual.aspis_core.field.square_n_loop.body,
    AspisR1M31Inverse.field.square_n_loop.body,multiply]
  rfl

/-- Generic loop association follows from equality of the step functions;
there is no concrete recurrence unfolding and no count bound. -/
theorem square_loop (iter : core.ops.range.Range Usize) (x : U32) :
    NEW_InverseActual.aspis_core.field.square_n_loop iter x =
      AspisR1M31Inverse.field.square_n_loop
        FIo_Native.aspis_core.field.M31.mul iter x := by
  unfold NEW_InverseActual.aspis_core.field.square_n_loop
    AspisR1M31Inverse.field.square_n_loop
  simp only [square_body]

theorem square (x : U32) (n : Usize) :
    NEW_InverseActual.aspis_core.field.square_n x n =
      AspisR1M31Inverse.field.square_n FIo_Native.aspis_core.field.M31.mul x n := by
  simp only [NEW_InverseActual.aspis_core.field.square_n,
    AspisR1M31Inverse.field.square_n,square_loop]

/-- Entire actual extracted inverse Result, including the zero assertion.
All raw U32 words are included; no caller output or nonzero premise. -/
theorem emitted (x : U32) :
    NEW_InverseActual.aspis_core.field.M31.inv x =
      AspisR1M31Inverse.field.M31.inv FIo_Native.aspis_core.field.M31.mul x := by
  simp only [NEW_InverseActual.aspis_core.field.M31.inv,
    AspisR1M31Inverse.field.M31.inv,multiply,square]

theorem cohort (x : U32) :
    NEW_InverseActual.aspis_core.field.M31.inv x =
      Port4C_InverseExecution.inverse_owned x :=
  (emitted x).trans (NFN_NBG_InverseBridge.inverse_result x)

theorem zero : NEW_InverseActual.aspis_core.field.M31.inv 0#u32 =
    fail .assertionFailure := by
  simp [NEW_InverseActual.aspis_core.field.M31.inv,massert]

#print axioms reducer
#print axioms multiply
#print axioms square_body
#print axioms square_loop
#print axioms square
#print axioms emitted
#print axioms cohort
#print axioms zero
#print axioms NEW_InverseActual.aspis_core.field.M31.inv
end NFN_NEW_InverseAssociation
-- END copied NEW_InverseAssociation
-- BEGIN copied LPi_Total: lean/LPi_Total.lean
set_option autoImplicit false
namespace AspisR1.NFN_LPi_Total
open Aeneas Aeneas.Std Result
abbrev NC := FIo_Native.aspis_core.field.CM31
abbrev NQ := FIo_Native.aspis_core.field.QM31
abbrev NE := FIo_Native.aspis_core.field.wide_exact.WideExact

def Total {α : Type} (r : Result α) : Prop := ∃ z, r = ok z

theorem bind_total {α β : Type} {r : Result α} {k : α → Result β}
    (hr : Total r) (hk : ∀ x, Total (k x)) : Total (r >>= k) := by
  obtain ⟨x,hx⟩ := hr
  rw [hx,bind_tc_ok]
  exact hk x

theorem m31_mul (x y : U32) : Total (FIo_Native.aspis_core.field.M31.mul x y) := by
  obtain ⟨z,h,_,_⟩ := NFN_LPf_BaseMultiply.source x y
  exact ⟨z,h⟩

theorem reduce (x : U64) : Total (FIo_Native.aspis_core.field.M31.reduce_u64 x) := by
  obtain ⟨z,h,_,_⟩ := NFN_LPf_CoreReduction.source x
  exact ⟨z,by simp only [FIo_Native.aspis_core.field.M31.reduce_u64,h,bind_tc_ok]⟩

theorem m31_add (x y : U32) : Total (FIo_Native.aspis_core.field.M31.add x y) := by
  simp only [FIo_Native.aspis_core.field.M31.add,lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem m31_sub (x y : U32) : Total (FIo_Native.aspis_core.field.M31.sub x y) := by
  simp only [FIo_Native.aspis_core.field.M31.sub,lift,bind_tc_ok]
  split <;> exact ⟨_,rfl⟩

theorem cm_add (x y : NC) : Total (FIo_Native.aspis_core.field.CM31.add x y) := by
  unfold FIo_Native.aspis_core.field.CM31.add
  apply bind_total (m31_add _ _); intro a
  apply bind_total (m31_add _ _); intro b
  exact ⟨_,rfl⟩

theorem cm_sub (x y : NC) : Total (FIo_Native.aspis_core.field.CM31.sub x y) := by
  unfold FIo_Native.aspis_core.field.CM31.sub
  apply bind_total (m31_sub _ _); intro a
  apply bind_total (m31_sub _ _); intro b
  exact ⟨_,rfl⟩

theorem cm_mul (x y : NC) : Total (FIo_Native.aspis_core.field.CM31.mul x y) := by
  unfold FIo_Native.aspis_core.field.CM31.mul
  apply bind_total (m31_mul _ _); intro a
  apply bind_total (m31_mul _ _); intro b
  simp only [lift,bind_tc_ok]
  apply bind_total (reduce _); intro c
  apply bind_total (m31_sub _ _); intro d
  apply bind_total (m31_sub _ _); intro e
  apply bind_total (m31_sub _ _); intro f
  exact ⟨_,rfl⟩

theorem by_r (x : NC) : Total (FIo_Native.aspis_core.field.mul_by_r x) := by
  unfold FIo_Native.aspis_core.field.mul_by_r FIo_Native.aspis_core.field.M31.double
  apply bind_total (m31_add _ _); intro a
  apply bind_total (m31_sub _ _); intro b
  apply bind_total (m31_add _ _); intro c
  apply bind_total (m31_add _ _); intro d
  exact ⟨_,rfl⟩

theorem qm_add (x y : NQ) : Total (FIo_Native.aspis_core.field.QM31.add x y) := by
  unfold FIo_Native.aspis_core.field.QM31.add
  apply bind_total (cm_add _ _); intro a
  apply bind_total (cm_add _ _); intro b
  exact ⟨_,rfl⟩

theorem qm_sub (x y : NQ) : Total (FIo_Native.aspis_core.field.QM31.sub x y) := by
  unfold FIo_Native.aspis_core.field.QM31.sub
  apply bind_total (cm_sub _ _); intro a
  apply bind_total (cm_sub _ _); intro b
  exact ⟨_,rfl⟩

theorem qm_mul (x y : NQ) : Total (FIo_Native.aspis_core.field.QM31.mul x y) := by
  unfold FIo_Native.aspis_core.field.QM31.mul
  apply bind_total (cm_mul _ _); intro a
  apply bind_total (cm_mul _ _); intro b
  apply bind_total (cm_add _ _); intro c
  apply bind_total (cm_add _ _); intro d
  apply bind_total (cm_mul _ _); intro e
  apply bind_total (by_r _); intro f
  apply bind_total (cm_add _ _); intro g
  apply bind_total (cm_sub _ _); intro h
  apply bind_total (cm_sub _ _); intro i
  exact ⟨_,rfl⟩

theorem mul_u (x : NQ) : Total (FIo_Native.aspis_core.field.wide_exact.mul_u x) := by
  unfold FIo_Native.aspis_core.field.wide_exact.mul_u
  apply bind_total (by_r _); intro a
  exact ⟨_,rfl⟩

theorem wide_mul (x y : NE) : Total (FIo_Native.aspis_core.field.wide_exact.WideExact.mul x y) := by
  unfold FIo_Native.aspis_core.field.wide_exact.WideExact.mul
  apply bind_total (qm_mul _ _); intro a
  apply bind_total (qm_mul _ _); intro b
  apply bind_total (qm_add _ _); intro c
  apply bind_total (qm_add _ _); intro d
  apply bind_total (qm_mul _ _); intro e
  apply bind_total (mul_u _); intro f
  apply bind_total (qm_add _ _); intro g
  apply bind_total (qm_sub _ _); intro h
  apply bind_total (qm_sub _ _); intro i
  exact ⟨_,rfl⟩

#print axioms bind_total
#print axioms m31_mul
#print axioms reduce
#print axioms m31_add
#print axioms m31_sub
#print axioms cm_add
#print axioms cm_sub
#print axioms cm_mul
#print axioms by_r
#print axioms qm_add
#print axioms qm_sub
#print axioms qm_mul
#print axioms mul_u
#print axioms wide_mul
end AspisR1.NFN_LPi_Total
-- END copied LPi_Total
-- BEGIN copied LPi_NatBase: lean/LPi_NatBase.lean
set_option autoImplicit false
namespace AspisR1.NFN_LPi_NatBase
open Aeneas Aeneas.Std Result

theorem sub_word (x y : U32) (h : y.val ≤ x.val) :
    (U32.wrapping_sub x y).val = x.val-y.val := by
  rw [U32.wrapping_sub_val_eq]
  have hx := x.hSize
  have hy := y.hSize
  have he : x.val+(UScalar.size .U32-y.val)=(x.val-y.val)+UScalar.size .U32 := by omega
  rw [he,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]

theorem add (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.add x y = ok z ∧
    z.val = (x.val+y.val)%2147483647 ∧ z.val < 2147483647 := by
  let s := U32.wrapping_add x y
  have sv : s.val = x.val+y.val := by
    rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
  simp only [FIo_Native.aspis_core.field.M31.add,FIo_Native.aspis_core.field.P,lift,bind_tc_ok]
  change ∃ z, (if s ≥ 2147483647#u32 then
    ok (U32.wrapping_sub s 2147483647#u32) else ok s) = ok z ∧ _
  by_cases h : s ≥ 2147483647#u32
  · rw [if_pos h]
    have hp : 2147483647 ≤ s.val := by scalar_tac
    refine ⟨_,rfl,?_,?_⟩
    · rw [sub_word s 2147483647#u32 hp]
      change s.val-2147483647 = (x.val+y.val)%2147483647
      rw [←sv,Nat.mod_eq_sub_mod hp,Nat.mod_eq_of_lt (by omega)]
    · rw [sub_word s 2147483647#u32 hp]; change s.val-2147483647 < 2147483647; omega
  · rw [if_neg h]
    have hp : s.val < 2147483647 := by scalar_tac
    exact ⟨_,rfl,by rw [←sv,Nat.mod_eq_of_lt hp],hp⟩

theorem sub (x y : U32) (hx : x.val < 2147483647) (hy : y.val < 2147483647) :
    ∃ z, FIo_Native.aspis_core.field.M31.sub x y = ok z ∧
    z.val = (x.val+2147483647-y.val)%2147483647 ∧ z.val < 2147483647 := by
  let a := U32.wrapping_add x 2147483647#u32
  have av : a.val = x.val+2147483647 := by
    rw [U32.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
    rfl
  let s := U32.wrapping_sub a y
  have sv : s.val = x.val+2147483647-y.val := by
    rw [sub_word _ _ (by omega),av]
  simp only [FIo_Native.aspis_core.field.M31.sub,FIo_Native.aspis_core.field.P,lift,bind_tc_ok]
  change ∃ z, (if s ≥ 2147483647#u32 then
    ok (U32.wrapping_sub s 2147483647#u32) else ok s) = ok z ∧ _
  by_cases h : s ≥ 2147483647#u32
  · rw [if_pos h]
    have hp : 2147483647 ≤ s.val := by scalar_tac
    refine ⟨_,rfl,?_,?_⟩
    · rw [sub_word s 2147483647#u32 hp]
      change s.val-2147483647 = (x.val+2147483647-y.val)%2147483647
      rw [←sv,Nat.mod_eq_sub_mod hp,Nat.mod_eq_of_lt (by omega)]
    · rw [sub_word s 2147483647#u32 hp]; change s.val-2147483647 < 2147483647; omega
  · rw [if_neg h]
    have hp : s.val < 2147483647 := by scalar_tac
    exact ⟨_,rfl,by rw [←sv,Nat.mod_eq_of_lt hp],hp⟩

#print axioms sub_word
#print axioms add
#print axioms sub
end AspisR1.NFN_LPi_NatBase
-- END copied LPi_NatBase
-- BEGIN copied LPi_CMProduct: lean/LPi_CMProduct.lean
set_option autoImplicit false
namespace AspisR1.NFN_LPi_CMProduct
open Aeneas Aeneas.Std Result NFN_LPi_Total
abbrev NC := FIo_Native.aspis_core.field.CM31

def Canon (x : NC) : Prop := x.a.val<2147483647 ∧ x.b.val<2147483647

def realWord (a b c d : Nat) := ((a*c)%2147483647+2147483647-(b*d)%2147483647)%2147483647
def imagWord (a b c d : Nat) :=
  ((((a+b)*(c+d))%2147483647+2147483647-(a*c)%2147483647)%2147483647+
    2147483647-(b*d)%2147483647)%2147483647

def sum (x : NC) : U64 := U64.wrapping_add
  (core.convert.num.FromU64U32.from x.a) (core.convert.num.FromU64U32.from x.b)
def cross (x y : NC) : U64 := U64.wrapping_mul (sum x) (sum y)

theorem sum_value (x : NC) : (sum x).val=x.a.val+x.b.val := by
  unfold sum
  rw [U64.wrapping_add_val_eq,Nat.mod_eq_of_lt (by scalar_tac)]
  rfl

theorem cross_value (x y : NC) (hx : Canon x) (hy : Canon y) :
    (cross x y).val=(x.a.val+x.b.val)*(y.a.val+y.b.val) := by
  unfold cross
  rw [U64.wrapping_mul_val_eq,sum_value,sum_value]
  apply Nat.mod_eq_of_lt
  have h0 : x.a.val+x.b.val < 4294967296 := by obtain ⟨_,_⟩ := hx; omega
  have h1 : y.a.val+y.b.val < 4294967296 := by obtain ⟨_,_⟩ := hy; omega
  have h := Nat.mul_lt_mul_of_lt_of_lt h0 h1
  norm_num [UScalar.size,UScalarTy.numBits,U64.size,U64.numBits] at h ⊢
  exact h

theorem source (x y : NC) (hx : Canon x) (hy : Canon y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y = ok z ∧ Canon z ∧
      z.a.val = realWord x.a.val x.b.val y.a.val y.b.val ∧
      z.b.val = imagWord x.a.val x.b.val y.a.val y.b.val := by
  obtain ⟨m0,h0,v0,c0⟩ := NFN_LPf_BaseMultiply.source x.a y.a
  obtain ⟨m1,h1,v1,c1⟩ := NFN_LPf_BaseMultiply.source x.b y.b
  obtain ⟨m2,h2,v2,c2⟩ := NFN_LPf_CoreReduction.source (cross x y)
  have hr : FIo_Native.aspis_core.field.M31.reduce_u64 (cross x y) = ok m2 := by
    simp only [FIo_Native.aspis_core.field.M31.reduce_u64,h2,bind_tc_ok]
  obtain ⟨a,ha,va,ca⟩ := NFN_LPi_NatBase.sub m0 m1 c0 c1
  obtain ⟨b,hb,vb,cb⟩ := NFN_LPi_NatBase.sub m2 m0 c2 c0
  obtain ⟨c,hc,vc,cc⟩ := NFN_LPi_NatBase.sub b m1 cb c1
  refine ⟨⟨a,c⟩,?_,⟨ca,cc⟩,?_,?_⟩
  · simp only [FIo_Native.aspis_core.field.CM31.mul,h0,h1,lift,bind_tc_ok]
    change (do let t ← FIo_Native.aspis_core.field.M31.reduce_u64 (cross x y)
               let a ← FIo_Native.aspis_core.field.M31.sub m0 m1
               let b ← FIo_Native.aspis_core.field.M31.sub t m0
               let c ← FIo_Native.aspis_core.field.M31.sub b m1
               ok (⟨a,c⟩ : NC)) = _
    simp only [hr,ha,hb,hc,bind_tc_ok]
  · simpa only [realWord,v0,v1] using va
  · rw [cross_value x y hx hy] at v2
    simpa only [imagWord,vb,v2,v0,v1] using vc

#print axioms sum_value
#print axioms cross_value
#print axioms source
end AspisR1.NFN_LPi_CMProduct
-- END copied LPi_CMProduct
-- BEGIN copied LPi_FieldValues: lean/LPi_FieldValues.lean
set_option autoImplicit false
namespace AspisR1.NFN_LPi_FieldValues
open Aeneas Aeneas.Std Result
abbrev NC := NFN_LPi_CMProduct.NC
abbrev NQ := NFN_LPi_Total.NQ
abbrev NE := NFN_LPi_Total.NE
abbrev CW := Nat × Nat
abbrev QW := CW × CW
abbrev EW := QW × QW
def cw (x : NC) : CW := (x.a.val,x.b.val)
def qw (x : NQ) : QW := (cw x.c0,cw x.c1)
def ew (x : NE) : EW := (qw x.c0,qw x.c1)
def canonC := NFN_LPi_CMProduct.Canon
def canonQ (x : NQ) : Prop := canonC x.c0 ∧ canonC x.c1
def canonE (x : NE) : Prop := canonQ x.c0 ∧ canonQ x.c1
def addM (a b : Nat) := (a+b)%2147483647
def subM (a b : Nat) := (a+2147483647-b)%2147483647
def addC (a b : CW) : CW := (addM a.1 b.1,addM a.2 b.2)
def subC (a b : CW) : CW := (subM a.1 b.1,subM a.2 b.2)
def mulC (a b : CW) : CW := (NFN_LPi_CMProduct.realWord a.1 a.2 b.1 b.2,
  NFN_LPi_CMProduct.imagWord a.1 a.2 b.1 b.2)
def byR (a : CW) : CW := (subM (addM a.1 a.1) a.2,addM a.1 (addM a.2 a.2))
def addQ (a b : QW) : QW := (addC a.1 b.1,addC a.2 b.2)
def subQ (a b : QW) : QW := (subC a.1 b.1,subC a.2 b.2)
def mulQ (a b : QW) : QW :=
  let ac := mulC a.1 b.1
  let bd := mulC a.2 b.2
  let cross := mulC (addC a.1 a.2) (addC b.1 b.2)
  (addC ac (byR bd),subC (subC cross ac) bd)
def mulU (a : QW) : QW := (byR a.2,a.1)
def mulE (a b : EW) : EW :=
  let ac := mulQ a.1 b.1
  let bd := mulQ a.2 b.2
  let cross := mulQ (addQ a.1 a.2) (addQ b.1 b.2)
  (addQ ac (mulU bd),subQ (subQ cross ac) bd)

theorem cm_mul (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul x y = ok z ∧ canonC z ∧
      cw z = mulC (cw x) (cw y) := by
  obtain ⟨z,h,c,a,b⟩ := NFN_LPi_CMProduct.source x y hx hy
  exact ⟨z,h,c,Prod.ext a b⟩

theorem cm_add (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.add x y = ok z ∧ canonC z ∧
      cw z = addC (cw x) (cw y) := by
  obtain ⟨a,ha,va,ca⟩ := NFN_LPi_NatBase.add x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := NFN_LPi_NatBase.add x.b y.b hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.add,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem cm_sub (x y : NC) (hx : canonC x) (hy : canonC y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.sub x y = ok z ∧ canonC z ∧
      cw z = subC (cw x) (cw y) := by
  obtain ⟨a,ha,va,ca⟩ := NFN_LPi_NatBase.sub x.a y.a hx.1 hy.1
  obtain ⟨b,hb,vb,cb⟩ := NFN_LPi_NatBase.sub x.b y.b hx.2 hy.2
  exact ⟨⟨a,b⟩,by simp only [FIo_Native.aspis_core.field.CM31.sub,ha,hb,bind_tc_ok],
    ⟨ca,cb⟩,Prod.ext va vb⟩

theorem by_r (x : NC) (hx : canonC x) :
    ∃ z, FIo_Native.aspis_core.field.mul_by_r x = ok z ∧ canonC z ∧ cw z = byR (cw x) := by
  obtain ⟨a,ha,va,ca⟩ := NFN_LPi_NatBase.add x.a x.a hx.1 hx.1
  obtain ⟨b,hb,vb,cb⟩ := NFN_LPi_NatBase.sub a x.b ca hx.2
  obtain ⟨c,hc,vc,cc⟩ := NFN_LPi_NatBase.add x.b x.b hx.2 hx.2
  obtain ⟨d,hd,vd,cd⟩ := NFN_LPi_NatBase.add x.a c hx.1 cc
  refine ⟨⟨b,d⟩,?_,⟨cb,cd⟩,?_⟩
  · simp only [FIo_Native.aspis_core.field.mul_by_r,FIo_Native.aspis_core.field.M31.double,
      ha,hb,hc,hd,bind_tc_ok]
  · exact Prod.ext (by simpa only [cw,byR,addM,subM,va] using vb) (by simpa only [cw,byR,addM,subM,vc] using vd)

#print axioms cm_mul
#print axioms cm_add
#print axioms cm_sub
#print axioms by_r
end AspisR1.NFN_LPi_FieldValues
-- END copied LPi_FieldValues
-- BEGIN copied NEA_FieldProduct: evidence/slice-q-leaves-20261029/NEA_FieldProduct.lean
set_option autoImplicit false
namespace NFN_NEA_FieldProduct
open Aeneas Aeneas.Std Result AspisR1.NFN_LPi_FieldValues
abbrev GC := AspisR1QueryGeometryActual.field.CM31
def toNative (x : GC) : NC := ⟨x.a,x.b⟩
def ofNative (x : NC) : GC := ⟨x.a,x.b⟩
def Canonical (x : GC) : Prop := x.a.val < 2147483647 ∧ x.b.val < 2147483647

def ops : AspisR1QueryGeometryActual.CM31Ops :=
  ⟨fun a b => ok ⟨a,b⟩, fun x y => do
    let z ← FIo_Native.aspis_core.field.CM31.mul (toNative x) (toNative y)
    ok (ofNative z)⟩

theorem emitted_cm (x y : GC) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, FIo_Native.aspis_core.field.CM31.mul (toNative x) (toNative y)=ok z ∧
      canonC z ∧ cw z=mulC (cw (toNative x)) (cw (toNative y)) := by
  exact AspisR1.NFN_LPi_FieldValues.cm_mul (toNative x) (toNative y) hx hy

theorem geometric_cm (x y : GC) (hx : Canonical x) (hy : Canonical y) :
    ∃ z, ops.mul x y=ok z ∧ Canonical z ∧
      (z.a.val,z.b.val)=mulC (x.a.val,x.b.val) (y.a.val,y.b.val) := by
  obtain ⟨z,run,canonical,value⟩ := emitted_cm x y hx hy
  refine ⟨ofNative z,?_,canonical,value⟩
  simp only [ops,run,bind_tc_ok]

#print axioms emitted_cm
#print axioms geometric_cm
end NFN_NEA_FieldProduct
-- END copied NEA_FieldProduct
-- BEGIN copied NEA_PointBridge: evidence/slice-q-leaves-20261029/NEA_PointBridge.lean
set_option autoImplicit false
namespace NFN_NEA_PointBridge
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual

def PacketDomain (u : Usize) : Prop := u.val < 262144

def record (a b : U32 × U32) (z : field.CM31) : Array U32 6#usize :=
  Array.make 6#usize [a.1,a.2,b.1,b.2,z.a,z.b]

/-- Reference-to-cohort association at the exact selected table inputs.
The product run is the named LOWER CM31 callee boundary, not a fibre-point
success premise. Canonical natural products are supplied by emitted_cm. -/
theorem selected (ops : CM31Ops) (u iA iB : Usize) (a b : U32 × U32)
    (z : field.CM31)
    (mask : lift (u &&& 511#usize)=ok iA)
    (shift : u >>> 9#i32=ok iB)
    (readA : Array.index_usize fast_domain.TABLE_A iA=ok a)
    (readB : Array.index_usize fast_domain.TABLE_B iB=ok b)
    (constructor : ∀ x y, ops.new x y=ok ⟨x,y⟩)
    (product : ops.mul ⟨a.1,a.2⟩ ⟨b.1,b.2⟩=ok z) :
    NEA_PointParam.point_ref u fast_domain.TABLE_A fast_domain.TABLE_B
        (Array.make 2#usize [z.a,z.b])=ok (record a b z) ∧
    fast_domain.fibre_point ops u=ok ⟨z.a,z.b⟩ := by
  rcases a with ⟨a0,a1⟩
  rcases b with ⟨b0,b1⟩
  constructor
  · simp only [NEA_PointParam.point_ref,mask,shift,readA,readB,bind_tc_ok]
    simp [Array.index_usize,Array.make,record]
  · simp only [fast_domain.fibre_point,domain.FibreIndex.get,mask,shift,
      readA,readB,fast_domain.table_value,constructor,bind_tc_ok]
    change (do let point ← ops.mul ⟨a0,a1⟩ ⟨b0,b1⟩
               ok ({x:=point.a,y:=point.b} : domain.Point field.M31)) = _
    rw [product]
    rfl

/-- Every admitted index determines both reads, without assuming a successful
geometry computation. Native K010 supplies the canonical selected table data;
only the lower product interpretation is then required. -/
theorem reads (u : Usize) (admitted : PacketDomain u) :
    ∃ iA iB a b,
      lift (u &&& 511#usize)=ok iA ∧ u >>> 9#i32=ok iB ∧
      Array.index_usize fast_domain.TABLE_A iA=ok a ∧
      Array.index_usize fast_domain.TABLE_B iB=ok b := by
  obtain ⟨ix,iA,iB,a,b,get,same,mask,_,shift,_,readA,readB⟩ :=
    R17FibrePointActualSuccess.source_indices_and_table_reads u admitted
  have eq : ix=u := by simpa [domain.FibreIndex.get] using (Result.ok.inj get).symm
  subst ix
  exact ⟨iA,iB,a,b,mask,shift,readA,readB⟩

#print axioms selected
#print axioms reads
end NFN_NEA_PointBridge
-- END copied NEA_PointBridge
-- BEGIN copied NEA_PointComplete: evidence/slice-q-leaves-20261029/NEA_PointComplete.lean
set_option autoImplicit false
namespace NFN_NEA_PointComplete
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual
open AspisR1.NFN_LPi_FieldValues NFN_NEA_FieldProduct

/-- Lower native CM31 bridge interpretation only. No geometry result or
successful enclosing call is a field. NBG/LPi supply this canonical law. -/
structure PhysicalInterpretation (cm : CM31Ops) : Prop where
  constructor : ∀ a b, cm.new a b=ok ⟨a,b⟩
  multiply : ∀ x y, Canonical x → Canonical y →
    ∃ z, cm.mul x y=ok z ∧ Canonical z ∧
      (z.a.val,z.b.val)=mulC (x.a.val,x.b.val) (y.a.val,y.b.val)

theorem emitted_interpretation : PhysicalInterpretation NFN_NEA_FieldProduct.ops :=
  ⟨fun _ _ => rfl,NFN_NEA_FieldProduct.geometric_cm⟩

theorem cohort (cm : CM31Ops) (physical : PhysicalInterpretation cm)
    (u : Usize) (admitted : NFN_NEA_PointBridge.PacketDomain u) :
    ∃ (a b : U32 × U32) (z : field.CM31),
      Canonical z ∧
      (z.a.val,z.b.val)=mulC (a.1.val,a.2.val) (b.1.val,b.2.val) ∧
      NEA_PointParam.point_ref u fast_domain.TABLE_A fast_domain.TABLE_B
        (Array.make 2#usize [z.a,z.b])=ok (NFN_NEA_PointBridge.record a b z) ∧
      fast_domain.fibre_point cm u=ok ⟨z.a,z.b⟩ := by
  obtain ⟨ix,iA,iB,a,b,get,same,mask,lo,shift,hi,readA,readB⟩ :=
    R17FibrePointActualSuccess.source_indices_and_table_reads u admitted
  have eq : ix=u := (Result.ok.inj get).symm
  subst ix
  have low : iA.val < 512 := by rw [lo]; exact Nat.mod_lt _ (by decide)
  have high : iB.val < 512 := by rw [hi]; unfold NFN_NEA_PointBridge.PacketDomain at admitted; omega
  have ca := NEA_TableCanonical.readA iA low a readA
  have cb := NEA_TableCanonical.readB iB high b readB
  obtain ⟨z,product,canonical,value⟩ := physical.multiply ⟨a.1,a.2⟩ ⟨b.1,b.2⟩ ca cb
  have both := NFN_NEA_PointBridge.selected cm u iA iB a b z mask shift readA readB
    physical.constructor product
  exact ⟨a,b,z,canonical,value,both.1,both.2⟩

#print axioms emitted_interpretation
#print axioms cohort
end NFN_NEA_PointComplete
-- END copied NEA_PointComplete

run_cmd do
 let env ← Lean.getEnv
 for (name, info) in env.constants do
  if info.isTheorem && (env.getModuleIdxFor? name).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent name)))
