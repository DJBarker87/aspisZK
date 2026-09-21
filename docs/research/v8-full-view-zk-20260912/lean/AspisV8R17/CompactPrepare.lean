import AspisV8R17.SourceOriginalWeights

/-! Reuse the source product-loop and transported-weight model for selected
ordinary entries. No dense vector is needed for the interpolant subtraction.
This does not identify Rust field arithmetic/indices with the model, or prove
the new descriptor's source encoding, Fiat--Shamir security, or privacy. -/
set_option autoImplicit false
namespace AspisV8R17.CompactPrepare
variable {F : Type*} [CommRing F]

def entry (points : Fin 3 → Fin 10 → F) (k : F)
    (inactive : Finset (Fin 1024)) (i : Fin 1024) : F :=
  (if i ∈ inactive then 1 else 0) +
    sourceMultilinearWeight k (points 0) i.val +
    sourceMultilinearWeight (k*k) (points 1) i.val +
    sourceMultilinearWeight ((k*k)*k) (points 2) i.val

theorem entry_eq_source (points : Fin 3 → Fin 10 → F) (k : F)
    (inactive : Finset (Fin 1024)) (g : Fin 1024 → F) (i : Fin 1024) :
    entry points k inactive i = sourceOriginalWeight points k inactive g false i := by
  rw [sourceOriginalWeight_eq]
  simp only [entry, sourceMultilinearWeight_eq, Bool.false_eq_true, ↓reduceIte]
  ring

def selected (points : Fin 3 → Fin 10 → F) (k : F)
    (inactive : Finset (Fin 1024)) (pivot : Fin 1024)
    (order : Fin 1024 ≃ Fin 1024) (j : Fin 1024) : F :=
  let r := order j
  if r ∈ inactive.erase pivot then
    entry points k inactive r - entry points k inactive pivot
  else entry points k inactive r

theorem selected_eq_source_dual (points : Fin 3 → Fin 10 → F) (k : F)
    (inactive : Finset (Fin 1024)) (pivot : Fin 1024)
    (order : Fin 1024 ≃ Fin 1024) (g : Fin 1024 → F) (j : Fin 1024) :
    selected points k inactive pivot order j =
      AspisV8R16.transportDual inactive pivot order
        (sourceOriginalWeight points k inactive g false) j := by
  simp only [selected, AspisV8R16.transportDual, entry_eq_source points k inactive g]

#print axioms entry_eq_source
#print axioms selected_eq_source_dual
end AspisV8R17.CompactPrepare
