import NJX_LeftRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_RecipientBody
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP)
open NJX_DigestResiduals (Digest Residuals)
/-- Actual recipient source computes4residuals THEN pack/product for each
of2groups. This body keeps that order, unlike the left global8prefix. -/
def group (cache : NP) (o : Residuals) (d : Digest) (g : Fin 2) : Result NQ := do
 let rs ← NJB_Traverse.run (fun j : Fin 4=>NJX_DigestResiduals.reference o d (NJX_DigestGroups.index g j)) (List.finRange 4)
 let r : Fin 4 → NQ := fun j=>rs.val[j.val]'(by rw [rs.property,List.length_finRange];exact j.isLt)
 let packed ← NJB_PackLaw.reference r
 FIq_Native.field.PreparedQm31Multiplier.mul cache packed

theorem group_source {high : NQ} {o : Residuals} {d : Digest} (p : NJX_DigestPacket.Packet high o d) (g : Fin 2) :
 group p.prepared o d g=ok (p.out g) := by
 have cells : ∀ j : Fin 4,NJX_DigestResiduals.reference o d (NJX_DigestGroups.index g j)=ok (p.residual (NJX_DigestGroups.index g j)) := by
  intro j
  obtain ⟨cl,cs⟩ := p.cells (NJX_DigestGroups.index g j)
  simp only [NJX_DigestResiduals.reference,cl,bind_tc_ok,cs]
 have seq := NJX_DigestPrefix.sequence _ (NJX_DigestGroups.group p.residual g) cells (List.finRange 4)
 have seq' : NJB_Traverse.run (fun j : Fin 4=>NJX_DigestResiduals.reference o d (NJX_DigestGroups.index g j)) (List.finRange 4)=
  ok ⟨List.ofFn (NJX_DigestGroups.group p.residual g),by simp⟩ := by
  rw [seq]
  rfl
 simp only [group,seq',bind_tc_ok,List.getElem_ofFn,p.packs,p.products]

def reference (high : NQ) (o : Residuals) (d : Digest) : Result (Fin 2 → NQ) := do
 let cache ← FIq_Native.field.PreparedQm31Multiplier.new high
 let x ← group cache o d 0
 let y ← group cache o d 1
 ok ![x,y]

theorem source {high : NQ} {o : Residuals} {d : Digest} (p : NJX_DigestPacket.Packet high o d) :
 reference high o d=ok p.out := by
 have vector : (![p.out 0,p.out 1] : Fin 2 → NQ)=p.out := by funext i;fin_cases i <;> rfl
 simp only [reference,p.constructor,bind_tc_ok,group_source,vector]
#print source
#print axioms group_source
#print axioms source
end AspisR1.NJX_RecipientBody
end
