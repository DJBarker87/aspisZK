import JGj_RawBounds
import JGj_ArrayCell
set_option autoImplicit false
namespace AspisR1.JGj_DotWordStep
open Aeneas Aeneas.Std Result WP
open FIq_Native
open FJb_TailCell (cell)
abbrev Raw4 := JGj_RawBounds.Raw
open AspisR1.ExtractedMaskReducerOps
open AspisV8R17.RawReducer (P)

def productBound : Nat := (P-1)^2
abbrev wide (x : U32) : U64 := UScalar.cast .U64 x

theorem wide_value (x : U32) : (wide x).val = x.val := by
  exact AspisR1.ExtractedMaskReducer.cast_widen_value x

theorem four_products_fit : 4*productBound < 2^64 := by
  norm_num [productBound,P]

def step (raw : Raw4) (word : U32) (scalar : U64) (limb : Usize) : Result Raw4 := do
  let weight ← lift (UScalar.cast .U64 word)
  let product ← UScalar.mul weight scalar
  let old ← Array.index_usize raw limb
  let value ← UScalar.add old product
  Array.update raw limb value

theorem source_success (raw : Raw4) (word : U32) (scalar : U64)
    (limb : Usize) (hi : limb.val < 4) (n : Nat) (hn : n ≤ 3)
    (hword : word.val < P) (hscalar : scalar.val < P)
    (hbudget : (cell raw (⟨limb.val,hi⟩ : Fin 4)).val ≤ n*productBound) :
    ∃ value : U64, step raw word scalar limb = .ok (raw.set limb value) ∧
      value.val = (cell raw (⟨limb.val,hi⟩ : Fin 4)).val + word.val*scalar.val ∧
      value.val ≤ (n+1)*productBound := by
  let index : Fin 4 := ⟨limb.val,hi⟩
  let old := cell raw index
  have hb : limb.val < (4#usize).val := by simpa using hi
  have hread : Array.index_usize raw limb = .ok old := by
    simpa only [old,index,cell] using RawPoseidonExternalRowReads.array_index_usize_ok raw limb hb
  have hprod : word.val*scalar.val ≤ productBound := by
    change word.val*scalar.val ≤ (P-1)*(P-1)
    exact Nat.mul_le_mul (Nat.le_pred_of_lt hword) (Nat.le_pred_of_lt hscalar)
  have hprod64 : (wide word).val*scalar.val < 2^64 := by
    rw [wide_value]
    have hsmall : productBound < 2^64 := by norm_num [productBound,P]
    exact Nat.lt_of_le_of_lt hprod hsmall
  obtain ⟨product,hmul,hproduct⟩ := mul_success (wide word) scalar hprod64
  rw [wide_value] at hproduct
  have hbudgetLocal : old.val ≤ n*productBound := hbudget
  have hsum : old.val+product.val ≤ (n+1)*productBound := by
    rw [hproduct,Nat.add_mul,Nat.one_mul]
    exact Nat.add_le_add hbudgetLocal hprod
  have hsum64 : old.val+product.val < 2^64 := by
    have hcount : n+1 ≤ 4 := by omega
    exact Nat.lt_of_le_of_lt (Nat.le_trans hsum (Nat.mul_le_mul_right productBound hcount)) four_products_fit
  obtain ⟨value,hadd,hvalue⟩ := add_success old product hsum64
  have hupdate : Array.update raw limb value = .ok (raw.set limb value) := by
    obtain ⟨out,hrun,hset⟩ := WP.spec_imp_exists (Array.update_spec raw limb value (by simpa [raw.property] using hb))
    simpa only [hset] using hrun
  refine ⟨value,?_,?_,?_⟩
  · simp only [step,wide,hmul,hread,hadd,hupdate,lift,bind_tc_ok]
  · exact hvalue.trans (congrArg (old.val + ·) hproduct)
  · rw [hvalue]
    exact hsum

#print axioms wide_value
#print axioms four_products_fit
#print axioms source_success
end AspisR1.JGj_DotWordStep
