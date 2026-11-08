import PV_LIB_A_ActiveDispatch17
set_option autoImplicit false
namespace PV_LIB_A_RootRead17
open PV_STX2_Syntax PV_STX2_Store
/-- A root read is symbolic Option identity. Do not kernel-reduce an entire
concrete Store to prove this equation at a single empty-path source address. -/
theorem root {W : Type} (C : Carrier W Data) (s : Store Data) (a n : Nat) :
    readAddress C s ⟨a,n,[]⟩ = s.cells ⟨a,n,[]⟩ := by
  unfold readAddress
  change (s.cells ⟨a,n,[]⟩).bind (fun value => some value) = s.cells ⟨a,n,[]⟩
  cases s.cells ⟨a,n,[]⟩ <;> rfl
#print axioms root
end PV_LIB_A_RootRead17
