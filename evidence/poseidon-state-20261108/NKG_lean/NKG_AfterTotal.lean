import NKG_Sum3Total
import RPv_FJh_ProjectedAfter
import RPv_JFy_ArrayTotal
import RPv_JFy_FieldTotal
import RPv_FIv_PreparedTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_AfterTotal
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ qm)
open FIv_NativeValue (Canon)
open FIv_PreparedNew (NP prepared)
open FIw_ArrayValue (canonical)
open ExtractedMaskPreparedState (PreparedFor)
open FJh_ProjectedAfter (Packed)
/-- Every field-call domain is derived on the SAME target, packs and caches. -/
theorem result (target internal theta : NQ) (lead full : Packed)
 (w : FJe_Sum3BridgeBase.Right) (p : Array NP 3#usize) (block : NP) (g : Usize)
 (hg : g.val<4) (ct : Canon target) (ci : Canon internal) (cb : Canon theta)
 (cl : canonical lead) (cf : canonical full) (cw : canonical w)
 (hp : ∀ i : Fin 3,PreparedFor (prepared (FJe_Sum3Value.cell p i)) (qm (FJe_Sum3Value.cell w i)))
 (hb : PreparedFor (prepared block) (qm theta)) :
 ∃ out,FJh_ProjectedAfter.source target internal lead full p block g=ok out ∧ Canon out := by
 obtain ⟨l,rl,lc⟩ := JFy_ArrayTotal.read lead g hg cl
 obtain ⟨dl,rdl,cdl,_⟩ := JFy_FieldTotal.sub target l ct lc
 obtain ⟨f,rf,fc⟩ := JFy_ArrayTotal.read full g hg cf
 obtain ⟨df,rdf,cdf,_⟩ := JFy_FieldTotal.sub target f ct fc
 obtain ⟨di,rdi,cdi,_⟩ := JFy_FieldTotal.sub target internal ct ci
 have cr : canonical (Array.make 3#usize [dl,df,di]) := by
   intro x hx
   simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
   rcases hx with rfl|rfl|rfl
   · exact cdl
   · exact cdf
   · exact cdi
 obtain ⟨sum,rs,cs⟩ := NKG_Sum3Total.result p (Array.make 3#usize [dl,df,di]) w cw cr hp
 obtain ⟨out,ro,co,_⟩ := FIv_PreparedTotal.mul block theta sum cb cs hb
 refine ⟨out,?_,co⟩
 simp only [FJh_ProjectedAfter.source,rl,rdl,rf,rdf,rdi,rs,ro,bind_tc_ok]
#print result
#print axioms result
end AspisR1.NKG_AfterTotal
end
