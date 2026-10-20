import CheckedWrappingScalarAgreement
import ExtractedCurrentReducer

set_option autoImplicit false
namespace AspisR1.EbyKDotPushCanonicalFoldBridgeV1
open Aeneas Aeneas.Std Result
open AspisR1.CheckedWrappingScalarAgreement
open AspisR1.ExtractedCurrentReducer

abbrev U64 := UScalar UScalarTy.U64

def high (x : U64) : U64 := ⟨x.bv.ushiftRight 31⟩
def wrappingFold (x : U64) : U64 :=
  UScalar.wrapping_add (UScalar.and x mask64) (high x)

theorem fold_agrees (x : U64) : foldExecution x = ok (wrappingFold x) := by
  obtain ⟨y,hy,_⟩ := foldExecution_success x
  have hs : UScalar.shiftRight x 31 = ok (high x) := by
    simp only [UScalar.shiftRight,high]; rfl
  have ha : UScalar.add (UScalar.and x mask64) (high x) = ok y := by
    simpa only [foldExecution,hs,bind_tc_ok] using hy
  have hw := (add_success_agrees _ _ _ ha).1
  simpa only [wrappingFold,hw] using hy

#print axioms fold_agrees
end AspisR1.EbyKDotPushCanonicalFoldBridgeV1
