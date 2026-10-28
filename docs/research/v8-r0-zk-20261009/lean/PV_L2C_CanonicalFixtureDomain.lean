import PV_L2C_FixtureOrigins
import PV_L2C_AccountEncode
import PV_L2C_ClientRoute
set_option autoImplicit false
noncomputable section
namespace PV_L2C_CanonicalFixtureDomain
open Aeneas Aeneas.Std Result R1Z R0Z.WriterRefine

/-- Explicit canonical-origin refinement of the original honest carrier.
It is broader than the selected planner's exact deterministic note search;
no equality of those two domains is asserted. -/
structure Origins (i : PV_Src_NativeInput.Input) : Prop where
  fields : PV_L2C_RecordRange.Fields i
  asset : (PV_Src_NativeInput.forestPublic i.request).asset = 77#u32
  accountFields : Nonempty (PV_L2C_AccountOrigins.Tree i.snapshot.current_root i.snapshot.frontier)

theorem tree : Nonempty (PV_L2C_AccountOrigins.Tree
    PV_RunJoin_FixtureArguments.snapshot.current_root PV_RunJoin_FixtureArguments.snapshot.frontier) := by
  refine ⟨PV_L2C_AccountEncode.tree _ _ ?_ ?_⟩
  · intro j hj;interval_cases j <;> decide
  · exact PV_RunJoin_AdmittedCarrier23.transfer_frontier
#print axioms tree

theorem transfer : Origins PV_RunJoin_AdmittedCarrier23.transfer :=
  ⟨PV_L2C_FixtureOrigins.transfer_fields,rfl,tree⟩
#print axioms transfer

theorem withdrawal : Origins PV_RunJoin_AdmittedCarrier23.withdrawal :=
  ⟨PV_L2C_FixtureOrigins.withdrawal_fields,rfl,tree⟩
#print axioms withdrawal

theorem rawP_excluded (t : PV_L2C_ClientRoute.Transfer) (j : Fin 8) :
    t.witness.recipient.owner_key.val[j.val]! ≠ 2147483647#u32 :=
  PV_L2C_DigestOrigin.excludes_P _ t.recipientOwner j
#print axioms rawP_excluded

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem both :
    (∃ i : PV_L2C_HonestCaller.Family (K:=K), i.val = PV_RunJoin_AdmittedCarrier23.transfer ∧ Origins i.val) ∧
    (∃ i : PV_L2C_HonestCaller.Family (K:=K), i.val = PV_RunJoin_AdmittedCarrier23.withdrawal ∧ Origins i.val) :=
  ⟨⟨⟨_,PV_L2C_FixtureAudit.transfer⟩,rfl,transfer⟩,
    ⟨⟨_,PV_L2C_FixtureAudit.withdrawal⟩,rfl,withdrawal⟩⟩
#print axioms both
end PV_L2C_CanonicalFixtureDomain
