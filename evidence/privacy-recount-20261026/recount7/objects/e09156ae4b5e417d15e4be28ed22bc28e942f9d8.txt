import R1Z.PV_Src_PortNodeResult
import R1Z.PV_Src_CanonicalFieldEquality
set_option autoImplicit false
namespace R1Z.PV_Src_PortParent
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort

theorem source (left right target : Array U32 8#usize)
    (hr : (right.val[7]!).val < 2147483647) (ht : Canon8 target)
    (hm : R0P.nodeCompress
      (fun i => liftU (K := ZMod 2147483647) left.val[i.val]!)
      (fun i => liftU right.val[i.val]!) =
      fun i => liftU target.val[i.val]!) :
    pool_v1.format.pool_v1_tree_parent
      (sourceExternalLinear := PV_Src_ExternalReference.dictionary) left right = ok target := by
  letI : Fact (Nat.Prime 2147483647) := ⟨R0Z.m31_prime⟩
  obtain ⟨out,ho,hc,hmeaning⟩ := PV_Src_PortNodeResult.source (K := ZMod 2147483647) left right hr
  have he : out=target := by
    apply BuilderRecordCanonical.array_ext
    intro j hj
    have h8 : j<8 := by simpa only [UScalar.ofNatCore_val_eq] using hj
    apply PV_Src_CanonicalFieldEquality.word _ _ (hc j h8) (ht j h8)
    exact (hmeaning ⟨j,h8⟩).trans (congrFun hm ⟨j,h8⟩)
  change poseidon2.merkle_node_compress_v3 (sourceExternalLinear := PV_Src_ExternalReference.dictionary) left right = ok target
  exact ho.trans (congrArg Result.ok he)

#print axioms source
end R1Z.PV_Src_PortParent
