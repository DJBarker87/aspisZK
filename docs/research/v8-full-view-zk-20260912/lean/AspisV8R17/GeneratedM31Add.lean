import AspisV8R17.GeneratedM31Sub

namespace V7Tag73CurrentHelpersOpaque
open Aeneas Aeneas.Std Result
-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::add"]
def aspis_core.field.M31.add
  (self : aspis_core.field.M31) (rhs : aspis_core.field.M31) :
  Result aspis_core.field.M31
  := do
  let s ← self + rhs
  if s >= aspis_core.field.P
  then let s1 ← s - aspis_core.field.P
       ok s1
  else ok s
-- END GENERATED

-- GENERATED FunsChunk04.lean
@[rust_fun "aspis_core::field::{aspis_core::field::M31}::double"]
def aspis_core.field.M31.double
  (self : aspis_core.field.M31) : Result aspis_core.field.M31 := do
  aspis_core.field.M31.add self self
-- END GENERATED
end V7Tag73CurrentHelpersOpaque

namespace AspisV8R17.GeneratedM31Add
open Aeneas.Std V7Tag73CurrentHelpersOpaque GeneratedM31Sub UnsignedCoreSlice RawReducer

theorem generated_add_mod (x y : aspis_core.field.M31)
    (hx : x.val < P) (hy : y.val < P) :
    ∃ r : aspis_core.field.M31, aspis_core.field.M31.add x y = .ok r ∧
      r.val = (x.val+y.val)%P ∧ r.val < P := by
  have p : P = 2147483647 := rfl
  have hbound : x.val+y.val < 2^32 := by omega
  have hadd : ∃ s : U32, UScalar.add x y = .ok s ∧ s.val = x.val+y.val :=
    tryMk_success _ hbound
  obtain ⟨s, hs, hvs⟩ := hadd
  obtain ⟨r, hr, hvr, hcr⟩ := finishSub_mod s (by rw [hvs]; omega)
  refine ⟨r, ?_, ?_, hcr⟩
  · change (do let s ← UScalar.add x y; finishSub s) = Result.ok r
    simp only [hs, bind_tc_ok, hr]
  · simpa only [hvs] using hvr

theorem generated_double_mod (x : aspis_core.field.M31) (hx : x.val < P) :
    ∃ r : aspis_core.field.M31, aspis_core.field.M31.double x = .ok r ∧
      r.val = (x.val+x.val)%P ∧ r.val < P :=
  generated_add_mod x x hx hx

#print axioms generated_add_mod
#print axioms generated_double_mod
end AspisV8R17.GeneratedM31Add
