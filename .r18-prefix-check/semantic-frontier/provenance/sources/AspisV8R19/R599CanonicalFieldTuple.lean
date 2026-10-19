import AspisV8R19.SamplerFieldDecode
import AspisV8R19.R445InitialBlockRejectionLaw
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false
namespace AspisV8R19.R599CanonicalFieldTuple
open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerFieldDecode
open AspisV8R19.R445InitialBlockRejectionLaw (modulus)
noncomputable section

def tupleField (x : Fin 4 → Fin modulus) : QM31Exact :=
  decode4 (x 0).val (x 1).val (x 2).val (x 3).val

def fieldTuple (q : QM31Exact) : Fin 4 → Fin modulus :=
  ![⟨q.re.re.val, ZMod.val_lt q.re.re⟩,
    ⟨q.re.im.val, ZMod.val_lt q.re.im⟩,
    ⟨q.im.re.val, ZMod.val_lt q.im.re⟩,
    ⟨q.im.im.val, ZMod.val_lt q.im.im⟩]

def tupleFieldEquiv : (Fin 4 → Fin modulus) ≃ QM31Exact where
  toFun := tupleField
  invFun := fieldTuple
  left_inv := by
    intro x
    funext i
    fin_cases i <;> apply Fin.ext <;>
      simp [fieldTuple, tupleField, decode4, Nat.mod_eq_of_lt]
  right_inv := by
    intro q
    apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · simp [tupleField, fieldTuple, decode4]
      · simp [tupleField, fieldTuple, decode4]
    · apply QuadraticAlgebra.ext
      · simp [tupleField, fieldTuple, decode4]
      · simp [tupleField, fieldTuple, decode4]

theorem tupleFieldEquiv_apply (x : Fin 4 → Fin modulus) :
    tupleFieldEquiv x = tupleField x := rfl

theorem ofFn_four_values (x : Fin 4 → Fin modulus) :
    (List.ofFn x).map Fin.val = [
      (x 0).val, (x 1).val, (x 2).val, (x 3).val] := by
  apply List.ext_getElem (by simp)
  intro n hn1 hn2
  have hn : n < 4 := by simpa using hn1
  interval_cases n <;> simp

theorem listDecode_tuple (x : Fin 4 → Fin modulus) :
    SamplerFieldDecode.decode ((List.ofFn x).map Fin.val) = tupleField x := by
  rw [ofFn_four_values]
  rfl

theorem decode_eq_tuple_iff {xs : List Nat} (hlen : xs.length = 4)
    (hcan : ∀ a ∈ xs, a < modulus) (x : Fin 4 → Fin modulus) :
    SamplerFieldDecode.decode xs = tupleField x ↔
      xs = (List.ofFn x).map Fin.val := by
  obtain ⟨a,b,c,d,hxs⟩ : ∃ a b c d, xs = [a,b,c,d] :=
    ⟨_,_,_,_,List.eq_getElem_of_length_eq_four xs hlen⟩
  subst xs
  constructor
  · intro h
    change decode4 a b c d = tupleField x at h
    have h0 := congrArg (fun z : QM31Exact => z.re.re) h
    have h1 := congrArg (fun z : QM31Exact => z.re.im) h
    have h2 := congrArg (fun z : QM31Exact => z.im.re) h
    have h3 := congrArg (fun z : QM31Exact => z.im.im) h
    simp only [tupleField, decode4] at h0 h1 h2 h3
    have hn0 : a = (x 0).val := by
      have := congrArg ZMod.val h0
      simpa only [ZMod.val_natCast_of_lt (hcan a (by simp)), ZMod.val_natCast_of_lt (x 0).isLt] using this
    have hn1 : b = (x 1).val := by
      have := congrArg ZMod.val h1
      simpa only [ZMod.val_natCast_of_lt (hcan b (by simp)), ZMod.val_natCast_of_lt (x 1).isLt] using this
    have hn2 : c = (x 2).val := by
      have := congrArg ZMod.val h2
      simpa only [ZMod.val_natCast_of_lt (hcan c (by simp)), ZMod.val_natCast_of_lt (x 2).isLt] using this
    have hn3 : d = (x 3).val := by
      have := congrArg ZMod.val h3
      simpa only [ZMod.val_natCast_of_lt (hcan d (by simp)), ZMod.val_natCast_of_lt (x 3).isLt] using this
    subst a; subst b; subst c; subst d
    exact (ofFn_four_values x).symm
  · intro h
    rw [h]
    exact listDecode_tuple x

theorem decode_eq_tuple_iff_eq_fin {xs : List Nat} (hlen : xs.length = 4)
    (hcan : ∀ a ∈ xs, a < modulus) (x : Fin 4 → Fin modulus) :
    SamplerFieldDecode.decode xs = tupleField x ↔
      xs = (List.ofFn x).map Fin.val :=
  decode_eq_tuple_iff hlen hcan x

#print axioms tupleFieldEquiv
#print axioms tupleFieldEquiv_apply
#print axioms ofFn_four_values
#print axioms listDecode_tuple
#print axioms decode_eq_tuple_iff
end
end AspisV8R19.R599CanonicalFieldTuple
