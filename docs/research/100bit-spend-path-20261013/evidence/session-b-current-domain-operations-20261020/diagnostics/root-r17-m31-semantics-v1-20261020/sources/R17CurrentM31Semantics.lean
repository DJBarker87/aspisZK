import R17FibrePointLineNodeActual
import ExtractedCurrentReducer

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace R17CurrentM31Semantics
open R17FibrePointLineNodeActual
abbrev M := AspisR1Qm31ArithmeticProbe.field.M31
abbrev P : Nat := AspisCircleGroupOrder.P

def decode (x : U32) : ZMod P := x.val

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem add_value (a b z : U32) (h : a + b = .ok z) :
    z.val = a.val + b.val := by
  have hs := UScalar.add_equiv a b
  rw [h] at hs
  simp only [Result.ok.injEq] at hs
  exact hs.2.1

private theorem sub_value (a b z : U32) (h : a - b = .ok z) :
    z.val + b.val = a.val := by
  have hs := UScalar.sub_equiv a b
  rw [h] at hs
  simp only [Result.ok.injEq] at hs
  rcases hs with ⟨hbound,hvalue,_⟩
  omega

private theorem add_decode (a b z : U32) (h : a + b = .ok z) :
    decode z = decode a + decode b := by
  simp only [decode, add_value a b z h, Nat.cast_add]

private theorem sub_decode (a b z : U32) (h : a - b = .ok z) :
    decode z = decode a - decode b := by
  have hv := sub_value a b z h
  have he : (z.val : ZMod P) + (b.val : ZMod P) = (a.val : ZMod P) := by
    rw [← Nat.cast_add, hv]
  exact eq_sub_iff_add_eq.mpr he

private theorem decode_sourceP : decode AspisR1Qm31ArithmeticProbe.field.P = 0 := by
  change ((2147483647 : Nat) : ZMod 2147483647) = 0
  exact ZMod.natCast_self _

def finish (n : U32) : Result U32 :=
  if n ≥ AspisR1Qm31ArithmeticProbe.field.P then do
    let z ← n - AspisR1Qm31ArithmeticProbe.field.P
    .ok z
  else .ok n

private theorem finish_decode (n z : U32) (h : finish n = .ok z) :
    decode z = decode n := by
  unfold finish at h
  split at h
  · rcases bind_ok_inv h with ⟨v,hsub,hout⟩
    have hv : v = z := Result.ok.inj hout
    subst z
    rw [sub_decode n AspisR1Qm31ArithmeticProbe.field.P v hsub, decode_sourceP, sub_zero]
  · have hv : n = z := Result.ok.inj h
    subst z
    rfl

theorem current_add_decode (a b z : M)
    (h : AspisR1Qm31ArithmeticProbe.field.M31.add a b = .ok z) :
    decode z = decode a + decode b := by
  change (do let n ← a + b; finish n) = .ok z at h
  rcases bind_ok_inv h with ⟨n,hadd,hfinish⟩
  rw [finish_decode n z hfinish, add_decode a b n hadd]

theorem current_sub_decode (a b z : M)
    (h : AspisR1Qm31ArithmeticProbe.field.M31.sub a b = .ok z) :
    decode z = decode a - decode b := by
  change (do let n ← a + AspisR1Qm31ArithmeticProbe.field.P
             let m ← n - b
             finish m) = .ok z at h
  rcases bind_ok_inv h with ⟨n,hadd,htail⟩
  rcases bind_ok_inv htail with ⟨m,hsub,hfinish⟩
  rw [finish_decode m z hfinish, sub_decode n b m hsub,
    add_decode a AspisR1Qm31ArithmeticProbe.field.P n hadd,
    decode_sourceP, add_zero]

theorem current_mul_decode (a b z : M)
    (h : AspisR1Qm31ArithmeticProbe.field.M31.mul a b = .ok z) :
    decode z = decode a * decode b := by
  obtain ⟨out,hout,hvalue,_⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod a b
  have he : out = z := Result.ok.inj (hout.symm.trans h)
  subst z
  change (out.val : ZMod P) = (a.val : ZMod P) * (b.val : ZMod P)
  rw [hvalue]
  simp only [P, AspisCircleGroupOrder.P, Nat.cast_mod, ZMod.natCast_self,
    mod_zero, Nat.cast_mul]

def operations : M31Ops where
  mul := AspisR1Qm31ArithmeticProbe.field.M31.mul
  double := AspisR1Qm31ArithmeticProbe.field.M31.double
  sub := AspisR1Qm31ArithmeticProbe.field.M31.sub

theorem operations_semantics : M31OpsSemantics operations := by
  constructor
  · intro a b z h
    exact current_mul_decode a b z h
  · intro a z h
    exact current_add_decode a a z h
  · intro a b z h
    exact current_sub_decode a b z h

#print axioms current_add_decode
#print axioms current_sub_decode
#print axioms current_mul_decode
#print axioms operations_semantics
end R17CurrentM31Semantics
