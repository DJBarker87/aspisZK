import XSe_BasisRows
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release XRk_ResultTools
set_option autoImplicit false
namespace XSe_BasisOuter
open XSe_BasisUpdate
/-- Full staged basis construction preserves canonicality at each doubling
cut; positive n is derived at the actual initialization below. -/
theorem source (m node : aspis_core.field.M31) (width n : Usize)
 (basis out : Basis) (canonical : Canonical basis) (positive : 0<n.val)
 (run : verifier.accumulate_batched_with_node_loop0 m node width basis n=ok out) :
 Canonical out := by
 unfold verifier.accumulate_batched_with_node_loop0 at run
 apply XRl_LoopInvariant.preserve _
  (fun s : aspis_core.field.M31 × Basis × Usize => Canonical s.2.1 ∧ 0<s.2.2.val)
  Canonical (fun s => width.val-s.2.2.val) ?_ (node,basis,n) out ⟨canonical,positive⟩ run
 intro state result hc hr
 rcases state with ⟨v,b,k⟩
 dsimp! only at hr hc ⊢
 unfold verifier.accumulate_batched_with_node_loop0.body at hr
 split at hr
 · rename_i active
   obtain ⟨b1,hrows,hr⟩ := bind_success _ _ _ hr
   obtain ⟨square,_,hr⟩ := bind_success _ _ _ hr
   obtain ⟨twice,_,hr⟩ := bind_success _ _ _ hr
   obtain ⟨v1,_,hr⟩ := bind_success _ _ _ hr
   obtain ⟨k1,hdouble,hr⟩ := bind_success _ _ _ hr
   cases Result.ok.inj hr
   have doubled : k1.val=k.val*2 := by scalar_tac
   have can := XSe_BasisRows.source ⟨0#usize,k⟩ v b b1 k hc.1 hrows
   refine ⟨⟨can,?_⟩,?_⟩
   · change 0<k1.val
     rw [doubled]
     omega
   · change width.val-k1.val<width.val-k.val
     change k.val<width.val at active
     rw [doubled]
     omega
 · cases Result.ok.inj hr
   exact hc.1
#print axioms source
end XSe_BasisOuter
