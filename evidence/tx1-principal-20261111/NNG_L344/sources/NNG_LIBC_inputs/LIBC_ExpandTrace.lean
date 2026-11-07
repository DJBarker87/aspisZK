import LIBC_ExpandValuesModel
set_option autoImplicit false
noncomputable section
namespace LIBC_ExpandTrace
open Aeneas Aeneas.Std Result NFU_Retarget
/-- The deterministic pointwise graph has the CLOSED native trace. Trace
existence is proved from the original inputs, never supplied as a premise. -/
theorem trace (src before : Slice U8) (bound : src.val.length≤1856)
 (aligned : src.val.length%16=0) (shape : before.val.length=2*src.val.length) :
 LPn.Expand.NativeTrace src.val before.val (src.val.length/16)
 (LIBC_ExpandValuesModel.output src before).val := by
 obtain ⟨after,ht⟩ := LPn.Expand.total src.val before.val (src.val.length/16)
 have inherited := LPn.Expand.to_inherited src.val before.val after _ ht
 have length := LPl.Expand.length src.val before.val after _ inherited
 let out : Slice U8 := ⟨after,by rw [length];exact before.property⟩
 have native := NFU_CompactLeaves.expand_result src before out bound aligned shape ht
 have direct := LIBC_ExpandValuesModel.source src before bound
 rw [if_pos ⟨aligned,shape⟩] at direct
 have same : out=LIBC_ExpandValuesModel.output src before :=
  congrArg Prod.snd (Result.ok.inj (native.symm.trans direct))
 have values := congrArg Subtype.val same
 change after=(LIBC_ExpandValuesModel.output src before).val at values
 rw [← values]
 exact ht
#print axioms trace
end LIBC_ExpandTrace
