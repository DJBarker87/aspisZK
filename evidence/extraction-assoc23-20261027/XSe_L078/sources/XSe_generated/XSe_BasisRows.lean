import XSe_BasisUpdate
import XSc_RangeMeasure
import XRl_LoopInvariant
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSe_BasisRows
open XSe_BasisUpdate
/-- Canonicality is preserved across every actual inner basis-write loop,
without unrolling the256-cell array. -/
theorem source (iter : core.ops.range.Range Usize) (node : aspis_core.field.M31)
 (basis out : Basis) (n : Usize) (canonical : Canonical basis)
 (run : verifier.accumulate_batched_with_node_loop0_loop0 iter node basis n=ok out) :
 Canonical out := by
 unfold verifier.accumulate_batched_with_node_loop0_loop0 at run
 apply XRl_LoopInvariant.preserve _
  (fun s : core.ops.range.Range Usize × Basis => Canonical s.2) Canonical
  (fun s => XSc_RangeMeasure.remaining s.1) ?_ (iter,basis) out canonical run
 intro state result hc hr
 rcases state with ⟨it,b⟩
 unfold verifier.accumulate_batched_with_node_loop0_loop0.body at hr
 obtain ⟨item,next,hnext,hr⟩ := pair_bind_success _ _ _ hr
 cases item with
 | none =>
   cases Result.ok.inj hr
   exact hc
 | some j =>
   obtain ⟨old,_,hr⟩ := bind_success _ _ _ hr
   obtain ⟨product,hproduct,hr⟩ := bind_success _ _ _ hr
   obtain ⟨index,_,hr⟩ := bind_success _ _ _ hr
   obtain ⟨after,hupdate,hr⟩ := bind_success _ _ _ hr
   cases Result.ok.inj hr
   refine ⟨XSe_BasisUpdate.source b after index product hc (multiply old node product hproduct) hupdate,?_⟩
   have h := XSc_RangeMeasure.advance it next j hnext
   change XSc_RangeMeasure.remaining next < XSc_RangeMeasure.remaining it
   omega
#print axioms source
end XSe_BasisRows
