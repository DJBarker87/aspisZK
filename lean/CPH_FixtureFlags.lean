import CPH_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_FixtureFlags
open Aeneas Aeneas.Std S2W_D189Entry CPH_FixtureData
/-- These source-relevant privileges hold simultaneously in the joint runtime
model on the receipt's actual physical keys. No cryptographic acceptance follows. -/
theorem privileges :
    (e1.records (e1.handles 2).1).owned.is_writable = true ∧
    (e1.records (e1.handles 2).1).owned.is_signer = false ∧
    (e2.records (e2.handles 6).1).owned.is_writable = false ∧
    (e2.records (e2.handles 6).1).owned.is_signer = false ∧
    (e1.records (e1.handles 2).1).owned.key = CPH_RecordedKeys.key 2 ∧
    (e2.records (e2.handles 6).1).owned.key = CPH_RecordedKeys.key 2 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms privileges
end AspisR1.CPH_FixtureFlags
end
