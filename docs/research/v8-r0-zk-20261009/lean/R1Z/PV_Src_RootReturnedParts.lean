import R1Z.PV_Src_RootReturned
set_option autoImplicit false
namespace R1Z.PV_Src_RootReturnedParts
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.BuilderModel
open BuilderForestAdmissionPort
variable {K : Type} [Field K]

theorem source (roots : BuilderRecordsReference.Roots)
    (h : @pool_v1.pair_trace.pair_empty_roots PV_Src_ExternalReference.dictionary = ok roots) :
    (∀ l : Fin 20, DigestLift roots.val[l.val]! (emptyRootK (K := K) l)) ∧
    (∀ l : Fin 20, Canon8 roots.val[l.val]!) := by
  rw [PV_Src_RootReturned.source roots h]
  exact ⟨PV_Src_CanonicalRoots.meaning,fun l => PV_Src_CanonicalRoots.canonical l.castSucc⟩

#print axioms source
end R1Z.PV_Src_RootReturnedParts
