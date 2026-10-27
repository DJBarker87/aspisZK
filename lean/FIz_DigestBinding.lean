import FIz_DigestRead
import FIy_PublicDigestStep
import R0P.Digest
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIz_DigestBinding
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIw_PublicModel (Selectors)
theorem value (s : Selectors) (a : Array FIv_NativeArithmetic.NQ 16#usize)
    (row : Fin 1024) (d : Array U32 8#usize) (old : Fin 8 → K) :
    FIy_PublicDigestStep.model s a row.val d old=
      R0P.digestAddBinding old (FIw_PublicModel.selector s row)
        (fun j=>FIv_NativeArray.value a j.val) 0 (FIw_PublicModel.digest d) := by
  funext j
  rw [FIy_PublicDigestStep.model,FIz_DigestRead.value d j]
  simp only [R0P.digestAddBinding,show (0 : Fin 9).val=0 from rfl,Nat.zero_add]
  rfl
#print axioms value
end AspisR1.FIz_DigestBinding
end
