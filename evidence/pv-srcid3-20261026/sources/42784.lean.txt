import R1Z.PV_Src_ExternalAssociation
set_option autoImplicit false
namespace R1Z.PV_Src_ParentInstalledExternal
open Aeneas Aeneas.Std Result R0Z.WriterRefine BuilderForestAdmissionPort

theorem source (external : ExternalLinear) (h : PV_Src_ExternalAssociation.Associated external)
    (left right target : Array U32 8#usize)
    (hr : (right.val[7]!).val < 2147483647) (ht : Canon8 target)
    (hm : R0P.nodeCompress
      (fun i => liftU (K := ZMod 2147483647) left.val[i.val]!)
      (fun i => liftU right.val[i.val]!) = fun i => liftU target.val[i.val]!) :
    @pool_v1.format.pool_v1_tree_parent external left right = ok target := by
  rw [PV_Src_ExternalAssociation.dictionary external h]
  exact PV_Src_PortParent.source left right target hr ht hm

#print axioms source
end R1Z.PV_Src_ParentInstalledExternal
