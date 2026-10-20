import R17CurrentM31Semantics
import ExtractedCurrentCM31Mul

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace R17CurrentCM31Semantics
open R17CurrentM31Semantics
open AspisR1.ExtractedCurrentCM31Mul
abbrev CM := AspisR1Qm31ArithmeticProbe.field.CM31

def decodeCM (x : CM) : ZMod P × ZMod P := (decode x.a,decode x.b)

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem uadd_value (a b z : U64) (h : (a + b : Result U64) = .ok z) :
    z.val = a.val + b.val := by
  have hs := UScalar.add_equiv a b
  rw [h] at hs
  exact hs.2.1

private theorem umul_value (a b z : U64) (h : (a * b : Result U64) = .ok z) :
    z.val = a.val * b.val := by
  have hs := UScalar.mul_equiv a b
  have hmul : UScalar.mul a b = .ok z := h
  rw [hmul] at hs
  exact hs.2.1

/-- Partial correctness of the existing generated widening fragment. No
canonicality or independently supplied operation successes are required. -/
theorem cross_fragment_value (a b : CM) (product : U64)
    (h : generatedCrossFragment a b = .ok product) :
    product.val = (a.a.val+a.b.val)*(b.a.val+b.b.val) := by
  rw [generatedCrossFragment_eq] at h
  unfold crossOperand at h
  rcases bind_ok_inv h with ⟨left,hl,htail⟩
  rcases bind_ok_inv htail with ⟨right,hr,hm⟩
  have hv := umul_value left right product hm
  rw [uadd_value _ _ left hl,uadd_value _ _ right hr,
    widen_value,widen_value,widen_value,widen_value] at hv
  exact hv

private theorem wrapper_decode (x : U64) (z : M)
    (h : AspisR1Qm31ArithmeticProbe.field.M31.reduce_u64 x = .ok z) :
    decode z = (x.val : ZMod P) := by
  obtain ⟨out,hout,hvalue,_⟩ := AspisR1.ExtractedCurrentReducer.current_wrapper_mod x
  have he : out = z := Result.ok.inj (hout.symm.trans h)
  subst z
  change (out.val : ZMod P) = (x.val : ZMod P)
  rw [hvalue]
  have hp : AspisV8R17.RawReducer.P = P := by
    norm_num [AspisV8R17.RawReducer.P,P,AspisCircleGroupOrder.P]
  rw [hp,ZMod.natCast_mod]

theorem current_cm31_mul_decode (a b z : CM)
    (h : AspisR1Qm31ArithmeticProbe.field.CM31.mul a b = .ok z) :
    decodeCM z = R17FibrePointDecodedProduct.cm31Product (decodeCM a) (decodeCM b) := by
  rw [generated_mul_graph] at h
  rcases bind_ok_inv h with ⟨m0,h0,hrest1⟩
  rcases bind_ok_inv hrest1 with ⟨m1,h1,hrest2⟩
  rcases bind_ok_inv hrest2 with ⟨product,hp,hrest3⟩
  rcases bind_ok_inv hrest3 with ⟨m2,h2,hrest4⟩
  rcases bind_ok_inv hrest4 with ⟨low,hl,hrest5⟩
  rcases bind_ok_inv hrest5 with ⟨high0,hh0,hrest6⟩
  rcases bind_ok_inv hrest6 with ⟨high,hh,hout⟩
  have he : (⟨low,high⟩ : CM) = z := Result.ok.inj hout
  subst z
  have hm0 := current_mul_decode a.a b.a m0 h0
  have hm1 := current_mul_decode a.b b.b m1 h1
  have hm2 := wrapper_decode product m2 h2
  rw [cross_fragment_value a b product hp,Nat.cast_mul,Nat.cast_add,Nat.cast_add] at hm2
  apply Prod.ext
  · change decode low = decode a.a * decode b.a - decode a.b * decode b.b
    rw [current_sub_decode m0 m1 low hl,hm0,hm1]
  · change decode high = decode a.a * decode b.b + decode a.b * decode b.a
    rw [current_sub_decode high0 m1 high hh,
      current_sub_decode m2 m0 high0 hh0,hm2,hm0,hm1]
    simp only [decode] at *
    ring

abbrev SourceCM := AspisR1QueryGeometryActual.field.CM31

def toArithmetic (x : SourceCM) : CM := ⟨x.a,x.b⟩
def fromArithmetic (x : CM) : SourceCM := ⟨x.a,x.b⟩

def operations : AspisR1QueryGeometryActual.CM31Ops where
  new := fun a b => .ok ⟨a,b⟩
  mul := fun a b => do
    let z ← AspisR1Qm31ArithmeticProbe.field.CM31.mul (toArithmetic a) (toArithmetic b)
    .ok (fromArithmetic z)

theorem operations_semantics : R17FibrePointDecodedProduct.CM31OpsSemantics operations := by
  constructor
  · intro a b c h
    have he : (⟨a,b⟩ : SourceCM) = c := Result.ok.inj h
    subst c
    rfl
  · intro a b c h
    change (do
      let z ← AspisR1Qm31ArithmeticProbe.field.CM31.mul (toArithmetic a) (toArithmetic b)
      .ok (fromArithmetic z)) = .ok c at h
    rcases bind_ok_inv h with ⟨z,hz,hout⟩
    have he : fromArithmetic z = c := Result.ok.inj hout
    subst c
    exact current_cm31_mul_decode (toArithmetic a) (toArithmetic b) z hz

#print axioms cross_fragment_value
#print axioms current_cm31_mul_decode
#print axioms operations_semantics
end R17CurrentCM31Semantics
