import NJX_DigestResiduals
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_DigestPrefix
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJX_DigestResiduals (Digest Residuals Cell reference)
/-- Generic deterministic sequencing lemma; the row root supplies every
child equation from its SAME arguments, never takes this interface as input. -/
theorem sequence {α β : Type} (f : α → Result β) (r : α → β)
 (hf : ∀ i,f i=ok (r i)) (js : List α) :
 NJB_Traverse.run f js=ok ⟨js.map r,by simp⟩ := by
 induction js with
 | nil => rfl
 | cons j js ih => simp only [NJB_Traverse.run,hf,ih,bind_tc_ok];rfl

/-- All8 actual lift/sub Results supply a deterministic ordered residual
prefix, with every intermediate canonicality/domain derived internally. -/
theorem source (o : Residuals) (d : Digest) (ho : ∀ i,Canon (o i)) (hd : ∀ i,(d i).val<2147483647) :
 ∃ r : Residuals,
 (∀ i,Cell o d i (r i)) ∧ (∀ i,Canon (r i)) ∧
 (∀ i,decode (r i)=decode (o i)-((d i).val : K)) ∧
 NJB_Traverse.run (reference o d) (List.finRange 8)=ok ⟨List.ofFn r,by simp⟩ := by
 choose r cr cl hr vr using NJX_DigestResiduals.cell o d ho hd
 refine ⟨r,cl,hr,vr,?_⟩
 rw [sequence (reference o d) r cr]
 rfl
#print source
#print axioms sequence
#print axioms source
end AspisR1.NJX_DigestPrefix
end
