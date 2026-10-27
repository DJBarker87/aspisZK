import R1Z.PV_CB_Op100Funs
import R1Z.PV_CB_Op101Funs
import AspisR1ProducerRelease47.Kernels49
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Join_NegTransport
open Aeneas Aeneas.Std Result

theorem sub (a b : U32) : core.num.U32.wrapping_sub a b = U32.wrapping_sub a b := by
  apply UScalar.eq_of_val_eq
  rw [core.num.U32.wrapping_sub_val_eq,U32.wrapping_sub_val_eq]
theorem mask_true (x : U32) :
    x &&& core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 true) = x := by
  change x &&& 4294967295#u32 = x
  rw [UScalar.eq_equiv_bv_eq]
  exact BitVec.and_allOnes
theorem mask_false (x : U32) :
    x &&& core.num.U32.wrapping_sub 0#u32 (UScalar.cast_fromBool .U32 false) = 0#u32 := by
  change x &&& 0#u32 = 0#u32
  exact U32.and_zero x

theorem scalar101 (x : U32) :
    PV_CB_ShippedOp101.aspis_core.field.M31.neg x = AspisR1ProducerRelease47.field.M31.neg x := by
  unfold PV_CB_ShippedOp101.aspis_core.field.M31.neg PV_CB_ShippedOp101.aspis_core.field.ct.neg
  simp only [lift,bind_tc_ok]
  by_cases h : x = 0#u32
  · subst x
    rw [show (0#u32 != 0#u32) = false from rfl,mask_false]
    rfl
  · have b : (x != 0#u32) = true := by simp [h]
    rw [b,mask_true]
    simp only [AspisR1ProducerRelease47.field.M31.neg,if_neg h,lift,bind_tc_ok]
    rw [sub,PV_CB_ShippedOp101.aspis_core.field.P,AspisR1ProducerRelease47.field.P]

theorem scalar100 (x : U32) :
    PV_CB_ShippedOp100.aspis_core.field.M31.neg x = AspisR1ProducerRelease47.field.M31.neg x := by
  refine Eq.trans ?_ (scalar101 x)
  unfold PV_CB_ShippedOp100.aspis_core.field.M31.neg PV_CB_ShippedOp100.aspis_core.field.ct.neg
    PV_CB_ShippedOp101.aspis_core.field.M31.neg PV_CB_ShippedOp101.aspis_core.field.ct.neg
    PV_CB_ShippedOp100.aspis_core.field.P PV_CB_ShippedOp101.aspis_core.field.P
  rfl

def retainedQNeg (x : AspisR1ProducerRelease47.field.QM31) : Result AspisR1ProducerRelease47.field.QM31 := do
  let a ← AspisR1ProducerRelease47.field.CM31.neg x.c0
  let b ← AspisR1ProducerRelease47.field.CM31.neg x.c1
  ok ⟨a,b⟩
def retainedWNeg (x : AspisR1ProducerRelease47.field.wide_exact.WideExact) :
    Result AspisR1ProducerRelease47.field.wide_exact.WideExact := do
  let a ← retainedQNeg x.c0
  let b ← retainedQNeg x.c1
  ok ⟨a,b⟩

def decodeC100 (x : PV_CB_ShippedOp100.aspis_core.field.CM31) : AspisR1ProducerRelease47.field.CM31 := ⟨x.a,x.b⟩
def decodeQ100 (x : PV_CB_ShippedOp100.aspis_core.field.QM31) : AspisR1ProducerRelease47.field.QM31 := ⟨decodeC100 x.c0,decodeC100 x.c1⟩
theorem complex100 (x : PV_CB_ShippedOp100.aspis_core.field.CM31) :
    (do let y ← PV_CB_ShippedOp100.aspis_core.field.CM31.neg x; ok (decodeC100 y)) =
      AspisR1ProducerRelease47.field.CM31.neg (decodeC100 x) := by
  simp only [PV_CB_ShippedOp100.aspis_core.field.CM31.neg,scalar100,AspisR1ProducerRelease47.field.CM31.neg,
    decodeC100,bind_assoc_eq,bind_tc_ok]
theorem quartic100 (x : PV_CB_ShippedOp100.aspis_core.field.QM31) :
    (do let y ← PV_CB_ShippedOp100.aspis_core.field.QM31.neg x; ok (decodeQ100 y)) = retainedQNeg (decodeQ100 x) := by
  unfold PV_CB_ShippedOp100.aspis_core.field.QM31.neg retainedQNeg decodeQ100
  rw [← complex100,← complex100]
  simp only [bind_assoc_eq,bind_tc_ok]

def decodeC101 (x : PV_CB_ShippedOp101.aspis_core.field.CM31) : AspisR1ProducerRelease47.field.CM31 := ⟨x.a,x.b⟩
def decodeQ101 (x : PV_CB_ShippedOp101.aspis_core.field.QM31) : AspisR1ProducerRelease47.field.QM31 := ⟨decodeC101 x.c0,decodeC101 x.c1⟩
theorem complex101 (x : PV_CB_ShippedOp101.aspis_core.field.CM31) :
    (do let y ← PV_CB_ShippedOp101.aspis_core.field.CM31.neg x; ok (decodeC101 y)) =
      AspisR1ProducerRelease47.field.CM31.neg (decodeC101 x) := by
  simp only [PV_CB_ShippedOp101.aspis_core.field.CM31.neg,scalar101,AspisR1ProducerRelease47.field.CM31.neg,
    decodeC101,bind_assoc_eq,bind_tc_ok]
theorem quartic101 (x : PV_CB_ShippedOp101.aspis_core.field.QM31) :
    (do let y ← PV_CB_ShippedOp101.aspis_core.field.QM31.neg x; ok (decodeQ101 y)) = retainedQNeg (decodeQ101 x) := by
  unfold PV_CB_ShippedOp101.aspis_core.field.QM31.neg retainedQNeg decodeQ101
  rw [← complex101,← complex101]
  simp only [bind_assoc_eq,bind_tc_ok]

def decodeW100 (x : PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact) :
    AspisR1ProducerRelease47.field.wide_exact.WideExact := ⟨decodeQ100 x.c0,decodeQ100 x.c1⟩
theorem wide100 (x : PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact) :
    (do let y ← PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact.neg x; ok (decodeW100 y)) =
      retainedWNeg (decodeW100 x) := by
  unfold PV_CB_ShippedOp100.aspis_core.field.wide_exact.WideExact.neg retainedWNeg decodeW100
  rw [← quartic100,← quartic100]
  simp only [bind_assoc_eq,bind_tc_ok]
#print axioms sub
#print axioms mask_true
#print axioms mask_false
#print axioms scalar101
#print axioms scalar100
#print axioms complex100
#print axioms quartic100
#print axioms complex101
#print axioms quartic101
#print axioms wide100
end R1Z.PV_Join_NegTransport
