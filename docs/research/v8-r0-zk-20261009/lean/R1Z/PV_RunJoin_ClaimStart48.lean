import R1Z.PV_RunJoin_ClaimList48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ClaimStart48
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_ClaimThread48 (Column Point)
variable [ExternalTypes] [ExternalFuns]

theorem complete (columns : Slice Column) (point : Point) (small : columns.length≤14336) :
    prover.opening_claim_bytes columns point=
      PV_RunJoin_ClaimList48.run point columns.val (alloc.vec.Vec.new U8) := by
  unfold prover.opening_claim_bytes
  simp only [lift,bind_tc_ok]
  rw [PV_RunJoin_ClaimThread48.complete columns point _ 0#usize columns.length small (by rfl)]
  rw [PV_RunJoin_ClaimList48.complete columns point columns.length _ 0#usize small (by rfl)]
  rfl
#print axioms complete
end R1Z.PV_RunJoin_ClaimStart48
