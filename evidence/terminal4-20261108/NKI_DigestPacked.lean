import NKI_DigestView
import NJX_LeftRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_DigestPacked
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJX_DigestCohort (O D dc)
def cohort (high : NQ) (o : O) (d : D) (start : Usize) (right : Bool) : Result (Fin 2 → NQ) := do
 let a ← FIq_Native.pool_v1.pair_forest_semantic_terminal.add_digest_binding
  (Array.repeat 8#usize FIq_Native.field.QM31.ZERO) high o start d right
 let x ← NJB_PackLaw.reference (NJX_LeftRoot.lane a 0)
 let y ← NJB_PackLaw.reference (NJX_LeftRoot.lane a 1)
 ok ![x,y]
/-- General offset/right association. Target equations are explicit intermediate
support parameters, discharged by the append root, never a root hypothesis. -/
theorem source (high : NQ) (o : O) (d : D) (start : Usize) (right : Bool)
 (hb : start.val+8≤16) (hh : Canon high) (ho : FIw_ArrayValue.canonical o) (hd : dc d)
 (t : Fin 8 → U32) (ht : ∀ i,(t i).val<2147483647)
 (vt : ∀ i,(t i).val=NKI_DigestView.target d right i) :
 ∃ p : NJX_DigestPacket.Packet high (NKI_DigestView.opened o start hb) t,
 NJX_DigestPacket.reference high (NKI_DigestView.opened o start hb) t=ok p.out ∧
 cohort high o d start right=ok p.out := by
 have hc : ∀ i,Canon (NKI_DigestView.opened o start hb i) := fun i=>NJB_ArrayCarrier.canonical_cell o ho _
 obtain ⟨p,pcall⟩ := NJX_DigestPacket.source high _ t hh hc ht
 obtain ⟨old,oldcall,hold,vold⟩ := NKI_DigestView.source high o d start right hb hh ho hd
 choose packed cp hp vp using (fun g : Fin 2=>NJB_PackLaw.result (NJX_LeftRoot.lane old g) (fun j=>NJB_ArrayCarrier.canonical_cell old hold _))
 have same : packed=p.out := by
  funext g
  apply NJB_DecodeInjective.qm _ _ (hp g) (p.out_canonical g)
  rw [vp,NJB_PackLinearity.model,p.out_value]
  have lv : (fun j=>decode (NJX_LeftRoot.lane old g j))=(fun j=>decode high*(decode (NKI_DigestView.opened o start hb (NJX_DigestGroups.index g j))-((t (NJX_DigestGroups.index g j)).val : K))) := by
   funext j
   rw [vt]
   exact vold _
  rw [lv,NJB_PackLinearity.scale]
 have vector : (![packed 0,packed 1] : Fin 2 → NQ)=p.out := by
  rw [same]
  funext g;fin_cases g <;> rfl
 refine ⟨p,pcall,?_⟩
 simp only [cohort,oldcall,cp,bind_tc_ok,vector]
#print source
#print axioms source
end AspisR1.NKI_DigestPacked
end
