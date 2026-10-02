import AspisR249R110Raw
import AspisV8R19.R240HalfExecution

/-! Selected private R110 primitive execution. This file does not model
Coeff110, its Option try machinery, vectors, batch inversion or acceptance. -/
set_option autoImplicit false
namespace AspisV8R19.R250PrivateBaseExecution
open Aeneas Aeneas.Std Result
open AspisV8R15.ExactTowerBase
open ComplexBaseExecution (encodeBase encodeBase_val encodeBase_cast eq_encodeBase)
open AspisR249R110Raw.circle_norm.joined_inverse.line_norm.r110_norm
open AspisV8R17.RawReducer (P)
noncomputable section

@[simp] theorem p110_val : P110.val = P := by simp [P110,P]

theorem input_complete (w : U32) :
    B.input w = if w.val < P then .ok (some w) else .ok none := by
  simp only [B.input,UScalar.lt_equiv,p110_val]

theorem input_encoded (x : M31Exact) :
    B.input (encodeBase x) = .ok (some (encodeBase x)) := by
  rw [input_complete,if_pos (ZMod.val_lt x)]

theorem half_word (w : U32) :
    B.half w = .ok (R228HalfEncoding.halfScalar w) := by
  change R240HalfExecution.rawBaseHalf w = _
  exact R240HalfExecution.base_half_word w

theorem half_encoded (x : M31Exact) :
    B.half (encodeBase x) = .ok (encodeBase (x/2)) := by
  rw [half_word,R228HalfEncoding.halfScalar_encode]

theorem reduce_encoded (x : U64) :
    B.reduce x = .ok (encodeBase (x.val : M31Exact)) := by
  simp only [B.reduce,R161WrappedMulExecution.reduce_encode,bind_tc_ok]

theorem mul_current (a b : U32) (ha : a.val < P) (hb : b.val < P) :
    B.mul a b = AspisR156FullFreeze.aspis_core.field.M31.mul a b := by
  simp only [B.mul,AspisR156FullFreeze.aspis_core.field.M31.mul,
    UScalar.lt_equiv,R159WideBaseExecution.p_val,ha,hb,if_true,P110,
    AspisR156FullFreeze.aspis_core.field.P]
  rfl

theorem mul_encoded (x y : M31Exact) :
    B.mul (encodeBase x) (encodeBase y) = .ok (encodeBase (x*y)) := by
  rw [mul_current _ _ (ZMod.val_lt x) (ZMod.val_lt y)]
  exact R161WrappedMulExecution.mul_encode x y

theorem add_raw (a b : U32) :
    B.add a b = AspisR156FullFreeze.aspis_core.field.r91_raw_add a b := by
  simp only [B.add,AspisR156FullFreeze.aspis_core.field.r91_raw_add,
    P110,AspisR156FullFreeze.aspis_core.field.P]

theorem sub_raw (a b : U32) :
    B.sub a b = AspisR156FullFreeze.aspis_core.field.r91_raw_sub a b := by
  simp only [B.sub,AspisR156FullFreeze.aspis_core.field.r91_raw_sub,
    P110,AspisR156FullFreeze.aspis_core.field.P]

def encodeC (z : CM31Exact) : C := (encodeBase z.re,encodeBase z.im)

theorem output_encoded (z : CM31Exact) :
    C.output (encodeC z) = .ok (R163ComplexExecution.encode z) := by
  rfl

#print axioms p110_val
#print axioms input_complete
#print axioms input_encoded
#print axioms half_word
#print axioms half_encoded
#print axioms reduce_encoded
#print axioms mul_current
#print axioms mul_encoded
#print axioms add_raw
#print axioms sub_raw
#print axioms output_encoded
end
end AspisV8R19.R250PrivateBaseExecution
