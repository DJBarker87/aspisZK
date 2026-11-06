import NJX_DigestResiduals
import NJB_PackLaw
import NJB_PackLinearity
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_DigestGroups
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIv_PreparedNew (NP)
def index (g : Fin 2) (j : Fin 4) : Fin 8 := ⟨4*g.val+j.val,by have:=g.isLt;have:=j.isLt;omega⟩
def group (r : Fin 8 → NQ) (g : Fin 2) : Fin 4 → NQ := fun j=>r (index g j)
def reference (p : NP) (r : Fin 8 → NQ) (g : Fin 2) : Result NQ := do
 let packed ← NJB_PackLaw.reference (group r g)
 FIq_Native.field.PreparedQm31Multiplier.mul p packed
/-- One actual4residual pack/product, paired with complete emitted Results. -/
theorem source (p : NP) (high : NQ) (r : Fin 8 → NQ) (g : Fin 2)
 (hh : Canon high) (hr : ∀ i,Canon (r i)) (hp : NJB_PreparedLaws.Domain p high) :
 ∃ packed out,NJB_PackLaw.reference (group r g)=ok packed ∧ Canon packed ∧
 FIq_Native.field.PreparedQm31Multiplier.mul p packed=ok out ∧ reference p r g=ok out ∧
 Canon out ∧ decode out=decode high*NJB_PackLinearity.pack (fun j=>decode (r (index g j))) := by
 obtain ⟨packed,cp,hp',vp⟩ := NJB_PackLaw.result (group r g) (fun j=>hr _)
 obtain ⟨out,co,ho,vo⟩ := NJB_PreparedLaws.mul_result p high packed hh hp' hp
 refine ⟨packed,out,cp,hp',co,by simp only [reference,cp,bind_tc_ok,co],ho,?_⟩
 rw [vo,vp,NJB_PackLinearity.model]
 rfl
#print source
#print axioms source
end AspisR1.NJX_DigestGroups
end
