import R1LiteralQueryRead
import R0C.V3.Q22Law

/-! Deterministic set view of a successful literal q22 list. This connects the
ordered strict reader to the old verifier's set-valued query projection; it
does not prove that an execution produces a valid query list. -/
set_option autoImplicit false
noncomputable section

namespace AspisR1.LiteralQueryReadFacts

open AspisR1.LiteralQueryRead
open AspisV8R19.R412LegalQueryEnumeration
open R0C.V3

theorem chalSet_eq_univ_image (xs : List Nat)
    (q : Fin 22 → Fin 262144)
    (hdecode : LiteralQueryRead.decode xs = some q) :
    Q22.chalSet (.ok xs) = Finset.univ.image q := by
  obtain ⟨horder, hinj⟩ := LiteralQueryRead.decode_success xs q hdecode
  have hvalid : xs.Nodup ∧ xs.length = 22 ∧ ∀ x ∈ xs, x < 262144 := by
    unfold LiteralQueryRead.decode at hdecode
    split_ifs at hdecode with h
    · exact h
  let u : LegalQuery := legalOfList xs hvalid.1 hvalid.2.1 hvalid.2.2
  have henum : enumQuery u = xs :=
    enum_legalOfList xs hvalid.1 hvalid.2.1 hvalid.2.2
  have hcoords : (fun j : Fin 22 => (u.val j).val) =
      (fun j : Fin 22 => (q j).val) := by
    apply List.ofFn_injective
    calc
      List.ofFn (fun j : Fin 22 => (u.val j).val) = xs := henum
      _ = List.ofFn (fun j : Fin 22 => (q j).val) := horder.symm
  change (R0C.QuerySampler.querySet xs).map
      ⟨Fin.cast (by norm_num), Fin.cast_injective _⟩ = Finset.univ.image q
  rw [← henum, R0C.QuerySampler.querySet_enum]
  ext x
  simp only [Finset.mem_map, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, ⟨j, rfl⟩, hy⟩
    refine ⟨j, ?_⟩
    apply Fin.ext
    have hyv := congrArg Fin.val hy
    simpa only [Fin.val_cast] using (congrFun hcoords j).symm.trans hyv
  · rintro ⟨j, rfl⟩
    refine ⟨u.val j, ⟨j, rfl⟩, ?_⟩
    apply Fin.ext
    exact congrFun hcoords j

theorem chalSet_card_eq_22 (xs : List Nat)
    (q : Fin 22 → Fin 262144)
    (hdecode : LiteralQueryRead.decode xs = some q) :
    (Q22.chalSet (.ok xs)).card = 22 := by
  rw [chalSet_eq_univ_image xs q hdecode]
  rw [Finset.card_image_of_injective _ (LiteralQueryRead.decode_success xs q hdecode).2]
  simp

#print axioms chalSet_eq_univ_image
#print axioms chalSet_card_eq_22

end AspisR1.LiteralQueryReadFacts
end
