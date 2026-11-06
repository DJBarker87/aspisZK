import NJB_PreparedLaws
import NJB_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_OccupancyContext
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open FIv_PreparedNew (NP)
structure Context where
 oneMinus : NQ
 both : NQ
 selected : NQ
 emptyValue : NQ
 empty : NP
def reference (input output occupied : NQ) : Result Context := do
 let oneMinus ← FIq_Native.field.QM31.sub FIq_Native.field.QM31.ONE occupied
 let both ← FIq_Native.field.QM31.add input output
 let selected ← FIq_Native.field.QM31.mul both occupied
 let emptyValue ← FIq_Native.field.QM31.sub both selected
 let empty ← FIq_Native.field.PreparedQm31Multiplier.new emptyValue
 ok ⟨oneMinus,both,selected,emptyValue,empty⟩
def Domain (c : Context) : Prop :=
 Canon c.oneMinus ∧ Canon c.both ∧ Canon c.selected ∧ Canon c.emptyValue ∧
 NJB_PreparedLaws.Domain c.empty c.emptyValue
/-- NJB_occupancy_context_proof K122/123 (exact attempt mapping in register):
five events, one cache; only the first four right operands are asserted. -/
def Cut (input output occupied : NQ) (r : Fin 4 → NQ) (cache : NP)
 (events : Fin 5 → NJB_Cuts.Event) (calls news : Nat) (out : Context) : Prop :=
 calls=5 ∧ news=1 ∧
 (∀ j,(events j).operation=(![2,1,0,2,3] : Fin 5 → Nat) j ∧
  (events j).left=(![FIq_Native.field.QM31.ONE,input,r 1,r 1,r 3] : Fin 5 → NQ) j) ∧
 (∀ j : Fin 4,(events j.castSucc).right=(![occupied,output,occupied,r 2] : Fin 4 → NQ) j) ∧
 out.oneMinus=r 0 ∧ out.both=r 1 ∧ out.selected=r 2 ∧ out.empty=cache
def Clauses (input output occupied : NQ) (c : Context) : Prop :=
 FIq_Native.field.QM31.sub FIq_Native.field.QM31.ONE occupied=ok c.oneMinus ∧
 FIq_Native.field.QM31.add input output=ok c.both ∧
 FIq_Native.field.QM31.mul c.both occupied=ok c.selected ∧
 FIq_Native.field.QM31.sub c.both c.selected=ok c.emptyValue ∧
 FIq_Native.field.PreparedQm31Multiplier.new c.emptyValue=ok c.empty
/-- Complete native prologue with the SAME cache domain and source-order field
clauses supplied internally. Empty factor equality holds for arbitrary canonical
occupied, not only binary occupied. -/
theorem source (input output occupied : NQ) (hi : Canon input) (ho : Canon output) (hc : Canon occupied) :
 ∃ c,reference input output occupied=ok c ∧ Domain c ∧ Clauses input output occupied c ∧
 (∃ r events,Cut input output occupied r c.empty events 5 1 c) ∧
 decode c.oneMinus=1-decode occupied ∧ decode c.both=decode input+decode output ∧
 decode c.selected=(decode input+decode output)*decode occupied ∧
 decode c.emptyValue=(decode input+decode output)*(1-decode occupied) := by
 obtain ⟨m,hm,cm,vm⟩ := NJB_StubLaws.qm_sub FIq_Native.field.QM31.ONE occupied FIv_NativeValue.one.1 hc
 obtain ⟨b,hb,cb,vb⟩ := NJB_StubLaws.qm_add input output hi ho
 obtain ⟨s,hs,cs,vs⟩ := NJB_StubLaws.qm_mul b occupied cb hc
 obtain ⟨e,he,ce,ve⟩ := NJB_StubLaws.qm_sub b s cb cs
 obtain ⟨p,hp,dp⟩ := NJB_PreparedLaws.new_result e ce
 let c : Context := ⟨m,b,s,e,p⟩
 let r : Fin 4 → NQ := ![m,b,s,e]
 let events : Fin 5 → NJB_Cuts.Event := fun j=>
  ⟨(![2,1,0,2,3] : Fin 5 → Nat) j,
   (![FIq_Native.field.QM31.ONE,input,b,b,e] : Fin 5 → NQ) j,
   (![occupied,output,occupied,s,FIq_Native.field.QM31.ZERO] : Fin 5 → NQ) j⟩
 refine ⟨c,?_,⟨cm,cb,cs,ce,dp⟩,⟨hm,hb,hs,he,hp⟩,?_,?_,vb,?_,?_⟩
 · simp only [reference,hm,hb,hs,he,hp,bind_tc_ok];rfl
 · refine ⟨r,events,rfl,rfl,?_,?_,rfl,rfl,rfl,rfl⟩
   · intro j;fin_cases j <;> exact ⟨rfl,rfl⟩
   · intro j;fin_cases j <;> rfl
 · simpa only [FIv_NativeValue.one.2] using vm
 · change decode s=(decode input+decode output)*decode occupied
   rw [vs,vb]
 · change decode e=(decode input+decode output)*(1-decode occupied)
   rw [ve,vs,vb]
   ring
#print source
#print axioms source
end AspisR1.NJL_OccupancyContext
end
