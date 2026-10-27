import R1Z.PV_Src_PortSboxStep
import R0Z.M31Prime

/-! Canonical words are uniquely determined by their M31 field values. -/
set_option autoImplicit false
namespace R1Z.PV_Src_CanonicalFieldEquality
open Aeneas Aeneas.Std Result R0Z.WriterRefine

theorem word (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647)
    (h : liftU (K := ZMod 2147483647) a = liftU b) : a=b := by
  unfold liftU at h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast,ZMod.val_natCast,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] at hv
  exact UScalar.eq_of_val_eq hv

theorem state (a b : Array U32 16#usize)
    (ha : PV_Src_PortSboxStep.Canonical a) (hb : PV_Src_PortSboxStep.Canonical b)
    (h : ∀ j : Fin 16, liftU (K := ZMod 2147483647) a.val[j.val]! =
      liftU b.val[j.val]!) : a=b := by
  apply BuilderRecordCanonical.array_ext
  intro j hj
  have h16 : j<16 := by simpa using hj
  exact word _ _ (ha ⟨j,h16⟩) (hb ⟨j,h16⟩) (h ⟨j,h16⟩)

#print axioms word
#print axioms state
end R1Z.PV_Src_CanonicalFieldEquality
