import NHH_QInverse
import NFG_QNegAssociation
set_option autoImplicit false
noncomputable section
namespace NHH_QNeg
open Aeneas Aeneas.Std Result
open AspisV8R19 AspisV8R15.ExactTowerBase
abbrev C := NFG_CheckedFieldRef.field.CM31
abbrev Q := NFG_CheckedFieldRef.field.QM31

def cm (x : C) : NHH_CMInverse.C := ⟨x.a,x.b⟩
def q (x : Q) : NHH_QInverse.Q := ⟨cm x.c0,cm x.c1⟩
def encodeC (x : CM31Exact) : C := ⟨ComplexBaseExecution.encodeBase x.re,ComplexBaseExecution.encodeBase x.im⟩
def encode (x : QM31Exact) : Q := ⟨encodeC x.re,encodeC x.im⟩
def toSampler (x : Q) := NHH_QInverse.toSampler (q x)

theorem cm_result (x : C) :
 (do let out ← NFG_CheckedFieldRef.field.CM31.neg x;ok (cm out))=
 NFG_InverseRef.field.CM31.neg (cm x) := by
 simp only [NFG_CheckedFieldRef.field.CM31.neg,NFG_CheckedFieldRef.field.M31.neg,
 NFG_CheckedFieldRef.field.P,NFG_InverseRef.field.CM31.neg,NFG_InverseRef.field.M31.neg,
 NFG_InverseRef.field.P,cm,bind_assoc_eq,bind_tc_ok]

theorem cm_encode (x : CM31Exact) :
 NFG_CheckedFieldRef.field.CM31.neg (encodeC x)=ok (encodeC (-x)) := by
 have h : Function.Injective cm := by intro a b e;cases a;cases b;cases e;rfl
 have assoc := cm_result (encodeC x)
 have enc : cm (encodeC x)=NHH_CMInverse.encode x := rfl
 rw [enc,NHH_CMAlgebra.negation] at assoc
 cases run : NFG_CheckedFieldRef.field.CM31.neg (encodeC x) with
 | ok out =>
  rw [run,bind_tc_ok] at assoc
  exact congrArg Result.ok (h (Result.ok.inj assoc))
 | fail e => rw [run] at assoc;cases assoc
 | div => rw [run] at assoc;cases assoc

/-- Exact four returned coordinates of the checked frozen helper. This does
not choose an absent adopted QM31.neg endpoint and earns no row closure. -/
theorem result (x : QM31Exact) :
 NFG_CheckedFieldRef.field.QM31.neg (encode x)=ok (encode (-x)) := by
 simp only [NFG_CheckedFieldRef.field.QM31.neg,encode,cm_encode,bind_tc_ok,
 QuadraticAlgebra.re_neg,QuadraticAlgebra.im_neg]

theorem coordinates (x : QM31Exact) :
 (do let out ← NFG_CheckedFieldRef.field.QM31.neg (encode x);ok (toSampler out))=
 ok (SamplerClosureProductExecution.encode (-x)) := by
 rw [result];rfl

def decode (x : Q) : QM31Exact := NHH_QInverse.decode (q x)
def Canon (x : Q) : Prop := NHH_QInverse.Canon (q x)
theorem q_injective : Function.Injective q := by
 have hcm : Function.Injective cm := by intro a b h;cases a;cases b;cases h;rfl
 intro x y h
 have a : x.c0=y.c0 := hcm (congrArg NFG_InverseRef.field.QM31.c0 h)
 have b : x.c1=y.c1 := hcm (congrArg NFG_InverseRef.field.QM31.c1 h)
 cases x;cases y;cases a;cases b;rfl

theorem roundtrip (x : Q) (hx : Canon x) : encode (decode x)=x := by
 apply q_injective
 exact NHH_QInverse.roundtrip (q x) hx

theorem canonical_result (x : Q) (hx : Canon x) :
 NFG_CheckedFieldRef.field.QM31.neg x=ok (encode (-decode x)) := by
 have h := result (decode x)
 rw [roundtrip x hx] at h
 exact h

#print axioms cm_result
#print axioms cm_encode
#print axioms result
#print axioms coordinates
#print axioms q_injective
#print axioms roundtrip
#print axioms canonical_result
end NHH_QNeg
end
