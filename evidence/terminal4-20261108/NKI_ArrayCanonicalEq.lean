import NJB_ArrayCarrier
import NJB_DecodeInjective
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_ArrayCanonicalEq
open Aeneas Aeneas.Std
open FIv_NativeArithmetic (NQ)
theorem source {N : Usize} (a b : Array NQ N)
 (ha : FIw_ArrayValue.canonical a) (hb : FIw_ArrayValue.canonical b)
 (values : FIw_ArrayValue.decoded a=FIw_ArrayValue.decoded b) : a=b := by
 have cells : NJB_ArrayCarrier.cell a=NJB_ArrayCarrier.cell b := by
  funext i
  exact NJB_DecodeInjective.qm _ _ (NJB_ArrayCarrier.canonical_cell a ha i) (NJB_ArrayCarrier.canonical_cell b hb i) (congrFun values i)
 calc
  a=NJB_ArrayCarrier.array (NJB_ArrayCarrier.cell a):=(NJB_ArrayCarrier.array_cell a).symm
  _=NJB_ArrayCarrier.array (NJB_ArrayCarrier.cell b):=congrArg NJB_ArrayCarrier.array cells
  _=b:=NJB_ArrayCarrier.array_cell b
#print axioms source
end AspisR1.NKI_ArrayCanonicalEq
end
