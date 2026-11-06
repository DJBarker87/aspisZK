import NJB_DecodeInjective
import NJX_DigestPacket
import NJX_DigestCohort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_LeftRoot
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJX_DigestCohort (O D ocells dcells dc)
def lane (a : Array NQ 8#usize) (g : Fin 2) (j : Fin 4) : NQ :=
 NJB_ArrayCarrier.cell a ⟨(NJX_DigestGroups.index g j).val,by have h:=(NJX_DigestGroups.index g j).isLt;scalar_tac⟩
def cohort (high : NQ) (o : O) (d : D) : Result (Fin 2 → NQ) := do
 let a ← FIq_Native.pool_v1.pair_forest_semantic_terminal.add_digest_binding
  (Array.repeat 8#usize FIq_Native.field.QM31.ZERO) high o 0#usize d false
 let x ← NJB_PackLaw.reference (lane a 0)
 let y ← NJB_PackLaw.reference (lane a 1)
 ok ![x,y]
/-- Complete242: one actual constructor, all8residuals, both packs/products,
exact complete2cell output equal to packing the SAME old emitted binding.
Only typed SAME input canonicality remains; every child clause discharged. -/
theorem source (high : NQ) (o : O) (d : D) (hh : Canon high)
 (ho : FIw_ArrayValue.canonical o) (hd : dc d) :
 ∃ p : NJX_DigestPacket.Packet high (ocells o) (dcells d),
 NJX_DigestPacket.reference high (ocells o) (dcells d)=ok p.out ∧
 cohort high o d=ok p.out := by
 have hc : ∀ i,Canon (ocells o i) := fun i=>NJB_ArrayCarrier.canonical_cell o ho _
 have hdc : ∀ i,(dcells d i).val<2147483647 := fun i=>hd _ (List.getElem_mem _)
 obtain ⟨p,pcall⟩ := NJX_DigestPacket.source high (ocells o) (dcells d) hh hc hdc
 obtain ⟨old,oldcall,hold,vold⟩ := NJX_DigestCohort.source high o d hh ho hd
 choose packed cp hp vp using (fun g : Fin 2=>NJB_PackLaw.result (lane old g) (fun j=>NJB_ArrayCarrier.canonical_cell old hold _))
 have same : packed=p.out := by
  funext g
  apply NJB_DecodeInjective.qm _ _ (hp g) (p.out_canonical g)
  rw [vp,NJB_PackLinearity.model,p.out_value]
  have lv : (fun j=>decode (lane old g j))=(fun j=>decode high*(decode (ocells o (NJX_DigestGroups.index g j))-((dcells d (NJX_DigestGroups.index g j)).val : K))) := by
   funext j
   exact vold _
  rw [lv,NJB_PackLinearity.scale]
 have vector : (![packed 0,packed 1] : Fin 2 → NQ)=p.out := by
  rw [same]
  funext g;fin_cases g <;> rfl
 refine ⟨p,pcall,?_⟩
 simp only [cohort,oldcall,cp,bind_tc_ok,vector]
#print source
#print axioms source
end AspisR1.NJX_LeftRoot
end
