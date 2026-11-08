import PV_LIB_A_ActivePrefix17
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_ActiveTransport17
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_LIB_SPEC_D984 PV_LIB_SPEC_Frozen
open PV_LIB_SPEC_ResourceHistory (Execution)
open PV_LIB_A_ActiveEnvironment17

/-- Any proved fresh source milestone excludes the old callback trap from
its complete earlier history. Symbolic induction, no finite-prefix unfolding. -/
theorem to_fresh (stack : PV_LIB_SPEC_PhysicalStack12.Frame) (x : Execution)
    (n m : Nat) (body : List PV_STX2_SliceSyntax.Node) (bound : m ≤ n)
    (fresh : PV_LIB_SPEC_LaneAJoins18.BodyEntry
      (PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack)
        PV_LIB_SPEC_ReachedEnvironment14.parameters n x) body) :
    run (PV_LIB_SPEC_TlsNative15.cut stack) PV_LIB_SPEC_ReachedEnvironment14.parameters m x =
      PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack)
        PV_LIB_SPEC_ReachedEnvironment14.parameters m x := by
  apply transport
  intro k hk
  rintro ⟨s,a,parents,pointer,w,events,eq⟩
  let q := PV_LIB_SPEC_ReachedNative14.run (PV_LIB_SPEC_TlsNative15.cut stack)
    PV_LIB_SPEC_ReachedEnvironment14.parameters k x
  have hq : q = ⟨PV_LIB_A_F5CallbackTrap16.waiting s a parents pointer w events,q.issued,q.consumed⟩ :=
    PV_LIB_A_F170Return16.execution_ext _ _ eq rfl rfl
  have noEntry := PV_LIB_A_F5CallbackTrap16.no_body_entry stack s a parents pointer w events
    q.issued q.consumed (n-k) body
  have kn : k ≤ n := Nat.le_trans (Nat.le_of_lt hk) bound
  rw [show n=k+(n-k) from (Nat.add_sub_of_le kn).symm,PV_LIB_SPEC_Original14.run_add] at fresh
  change PV_LIB_SPEC_LaneAJoins18.BodyEntry (PV_LIB_SPEC_ReachedNative14.run _ _ (n-k) q) body at fresh
  rw [hq] at fresh
  exact noEntry fresh

#print axioms to_fresh
end PV_LIB_A_ActiveTransport17
