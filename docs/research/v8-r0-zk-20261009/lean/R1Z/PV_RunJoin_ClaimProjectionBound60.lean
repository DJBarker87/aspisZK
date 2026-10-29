import R1Z.PV_RunJoin_ActualPlanSources59
import R1Z.PV_RunJoin_CompactCompleteBound60
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ClaimProjectionBound60
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

/-- The claim projection's fallback is included. This does not assume the
compact call succeeded or identify a caller's claim bytes. -/
theorem claim (p : prover.Publication) (n : Nat)
    (length : p.y1.length=32*n) (room : 16*n≤Usize.max) :
    Post (fun out => out.length≤16*n) (PV_RunJoin_ActualPlanSources59.compactClaim p) := by
  have hb := PV_RunJoin_CompactCompleteBound60.encode (alloc.vec.Vec.deref p.y1)
    PV_RunJoin_ActualPlanSources59.empty n length (by change 0+16*n≤Usize.max;omega)
  unfold PV_RunJoin_ActualPlanSources59.compactClaim
  cases h : host_compact.compact_values (alloc.vec.Vec.deref p.y1) PV_RunJoin_ActualPlanSources59.empty with
  | fail e => simp only [h,bind_tc_fail];trivial
  | div => simp only [h,bind_tc_div];trivial
  | ok pair =>
    rcases pair with ⟨status,next⟩
    rw [h] at hb
    simp only [bind_tc_ok,Aeneas.Std.uncurry]
    cases status with
    | Err e => change 0≤16*n;omega
    | Ok u =>
      change next.length≤0+16*n at hb
      change next.length≤16*n
      omega

#print axioms claim
end R1Z.PV_RunJoin_ClaimProjectionBound60
