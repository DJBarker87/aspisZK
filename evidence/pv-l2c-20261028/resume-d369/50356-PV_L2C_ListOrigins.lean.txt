import PV_L2C_DigestList
import PV_L2C_DigestOrigin
set_option autoImplicit false
namespace PV_L2C_ListOrigins
open Aeneas Aeneas.Std Result PV_L2C_DigestList

theorem success (bytes : List Bytes) (ds : List Digest)
    (h : run bytes = ok (.Ok ds)) : ∀ d ∈ ds, PV_L2C_DigestOrigin.Origin d := by
  induction bytes generalizing ds with
  | nil => cases h;simp
  | cons b bs ih =>
    rw [run] at h
    pv_peel h with first hf
    cases first with
    | Err e => cases h
    | Ok d =>
      pv_peel h with rest hr
      cases rest with
      | Err e => cases h
      | Ok tail =>
        cases h
        intro v hv
        rcases List.mem_cons.mp hv with he | ht
        · subst v;exact .decoded b hf
        · exact ih tail hr v ht
#print axioms success

theorem field (bytes : List Bytes) (ds : List Digest) (h : run bytes = ok (.Ok ds))
    (j : Nat) (hj : j < ds.length) : PV_L2C_DigestOrigin.Origin ds[j] :=
  success bytes ds h ds[j] (List.getElem_mem hj)
#print axioms field
end PV_L2C_ListOrigins
