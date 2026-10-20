import CuSavingsWideCore
import ExtractedMaskQM31SquareExact
import ExtractedMaskScalarExact
/-! Coordinate-only transport from the actual newly emitted square/scalar
operations to the retained raw-source exact contracts. No replacement square
implementation or arithmetic equivalence assumption is introduced. -/
set_option autoImplicit false
namespace AspisR1.CuSavingsWideArithmetic
open Aeneas Aeneas.Std Result AspisR1WideArithmetic
abbrev MaskC := AspisR1SelectedMaskProbe.field.CM31
abbrev MaskK := AspisR1SelectedMaskProbe.field.QM31

def toMaskC (x : field.CM31) : MaskC := ⟨x.a,x.b⟩
def fromMaskC (x : MaskC) : field.CM31 := ⟨x.a,x.b⟩
def toMaskK (x : K) : MaskK := ⟨toMaskC x.c0,toMaskC x.c1⟩
def fromMaskK (x : MaskK) : K := ⟨fromMaskC x.c0,fromMaskC x.c1⟩

private theorem scalar_add (x y : U32) :
    field.M31.add x y = AspisR1SelectedMaskProbe.field.M31.add x y := by
  unfold field.M31.add AspisR1Qm31ArithmeticProbe.field.M31.add
    AspisR1SelectedMaskProbe.field.M31.add
  simp only [AspisR1Qm31ArithmeticProbe.field.P,AspisR1SelectedMaskProbe.field.P]

private theorem scalar_sub (x y : U32) :
    field.M31.sub x y = AspisR1SelectedMaskProbe.field.M31.sub x y := by
  unfold field.M31.sub AspisR1SelectedMaskProbe.field.M31.sub
  simp only [field.P,AspisR1SelectedMaskProbe.field.P]

private theorem scalar_reduce (x : U64) :
    field.reduce_u64 x = AspisR1SelectedMaskProbe.field.reduce_u64 x := by
  unfold field.reduce_u64 AspisR1SelectedMaskProbe.field.reduce_u64
  simp only [field.P,AspisR1SelectedMaskProbe.field.P]

private theorem scalar_mul (x y : U32) :
    field.M31.mul x y = AspisR1SelectedMaskProbe.field.M31.mul x y := by
  unfold field.M31.mul AspisR1Qm31ArithmeticProbe.field.M31.mul
    AspisR1SelectedMaskProbe.field.M31.mul
  simp only [AspisR1Qm31ArithmeticProbe.field.reduce_u64,
    AspisR1Qm31ArithmeticProbe.field.P,AspisR1SelectedMaskProbe.field.reduce_u64,
    AspisR1SelectedMaskProbe.field.P]

private theorem scalar_double (x : U32) :
    field.M31.double x = AspisR1SelectedMaskProbe.field.M31.double x := by
  simp only [field.M31.double,AspisR1SelectedMaskProbe.field.M31.double,scalar_add]

private theorem cm_add_transport (x y : field.CM31) :
    field.CM31.add x y = (do
      let z ← AspisR1SelectedMaskProbe.field.CM31.add (toMaskC x) (toMaskC y)
      .ok (fromMaskC z)) := by
  simp only [field.CM31.add,AspisR1Qm31ArithmeticProbe.field.CM31.add,
    AspisR1SelectedMaskProbe.field.CM31.add,toC,fromC,toMaskC,fromMaskC,
    scalar_add,bind_assoc_eq,bind_tc_ok]

private theorem cm_mul_transport (x y : field.CM31) :
    field.CM31.mul x y = (do
      let z ← AspisR1SelectedMaskProbe.field.CM31.mul (toMaskC x) (toMaskC y)
      .ok (fromMaskC z)) := by
  simp only [field.CM31.mul,AspisR1Qm31ArithmeticProbe.field.CM31.mul,
    AspisR1SelectedMaskProbe.field.CM31.mul,toC,fromC,toMaskC,fromMaskC,
    scalar_mul,bind_assoc_eq,bind_tc_ok,
    AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64,
    AspisR1SelectedMaskProbe.field.M31.reduce_u64,
    AspisR1Qm31ArithmeticProbe.field.M31.sub,
    AspisR1SelectedMaskProbe.field.M31.sub,
    AspisR1Qm31ArithmeticProbe.field.reduce_u64,
    AspisR1SelectedMaskProbe.field.reduce_u64,
    AspisR1Qm31ArithmeticProbe.field.P,AspisR1SelectedMaskProbe.field.P]

private theorem cm_square_transport (x : field.CM31) :
    field.CM31.square x = (do
      let z ← AspisR1SelectedMaskProbe.field.CM31.square (toMaskC x)
      .ok (fromMaskC z)) := by
  simp only [field.CM31.square,AspisR1SelectedMaskProbe.field.CM31.square,
    toMaskC,fromMaskC,field.M31.reduce_u64,
    AspisR1SelectedMaskProbe.field.M31.reduce_u64,scalar_reduce,
    scalar_mul,scalar_double,field.P,AspisR1SelectedMaskProbe.field.P,
    bind_assoc_eq,bind_tc_ok]

private theorem cm_r_transport (x : field.CM31) :
    field.mul_by_r x = (do
      let z ← AspisR1SelectedMaskProbe.field.mul_by_r (toMaskC x)
      .ok (fromMaskC z)) := by
  simp only [field.mul_by_r,AspisR1SelectedMaskProbe.field.mul_by_r,
    toMaskC,fromMaskC,scalar_double,scalar_sub,scalar_add,
    bind_assoc_eq,bind_tc_ok]

theorem k_square_transport (x : K) :
    field.QM31.square x = (do
      let z ← AspisR1SelectedMaskProbe.field.QM31.square (toMaskK x)
      .ok (fromMaskK z)) := by
  simp only [field.QM31.square,AspisR1SelectedMaskProbe.field.QM31.square,
    field.CM31.double,AspisR1SelectedMaskProbe.field.CM31.double,
    cm_square_transport,cm_mul_transport,cm_add_transport,cm_r_transport,
    toMaskK,fromMaskK,toMaskC,fromMaskC,bind_assoc_eq,bind_tc_ok]

theorem k_square (x : K) (hx : CanonicalK x) :
    ∃ z,field.QM31.square x=.ok z ∧ CanonicalK z ∧ decodeK z=decodeK x*decodeK x := by
  have hm : ExtractedMaskQM31SquareExact.CanonicalQM (toMaskK x) := hx
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskQM31SquareExact.current_qm_square_exact (toMaskK x) hm
  refine ⟨fromMaskK z,?_,hc,hv⟩
  rw [k_square_transport,hz]
  rfl

private theorem cm_scalar_transport (x : field.CM31) (scalar : U32) :
    field.CM31.mul_m31 x scalar = (do
      let z ← AspisR1SelectedMaskProbe.field.CM31.mul_m31 (toMaskC x) scalar
      .ok (fromMaskC z)) := by
  simp only [field.CM31.mul_m31,AspisR1SelectedMaskProbe.field.CM31.mul_m31,
    toMaskC,fromMaskC,scalar_mul,bind_assoc_eq,bind_tc_ok]

theorem k_mul_m31_transport (x : K) (scalar : U32) :
    field.QM31.mul_m31 x scalar = (do
      let z ← AspisR1SelectedMaskProbe.field.QM31.mul_m31 (toMaskK x) scalar
      .ok (fromMaskK z)) := by
  simp only [field.QM31.mul_m31,AspisR1SelectedMaskProbe.field.QM31.mul_m31,
    cm_scalar_transport,toMaskK,fromMaskK,toMaskC,fromMaskC,
    bind_assoc_eq,bind_tc_ok]

def scalarK (scalar : U32) : ExactK := ExtractedMaskScalarExact.scalarEmbedding scalar

/-- Complete actual scalar operation; its per-limb multiplication/reduction
also canonicalizes noncanonical input words, so no caller canonicality premise
is necessary for this exact result. -/
theorem k_mul_m31 (x : K) (scalar : U32) :
    ∃ z,field.QM31.mul_m31 x scalar=.ok z ∧ CanonicalK z ∧
      decodeK z=decodeK x*scalarK scalar := by
  obtain ⟨z,hz,hc,hv⟩ := ExtractedMaskScalarExact.current_qm_mul_m31_exact (toMaskK x) scalar
  refine ⟨fromMaskK z,?_,hc,hv⟩
  rw [k_mul_m31_transport,hz]
  rfl

#print axioms k_mul_m31_transport
#print axioms k_mul_m31
#print axioms k_square_transport
#print axioms k_square
end AspisR1.CuSavingsWideArithmetic
