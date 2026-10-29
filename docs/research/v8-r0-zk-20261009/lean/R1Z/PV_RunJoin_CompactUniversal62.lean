import R1Z.PV_RunJoin_ClaimProjectionBound60
import R1Z.PV_RunJoin_CompactLengthReject40
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CompactUniversal62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41

/-- Every complete compact-values Result, including partial error returns,
fits within the supplied logical byte bound. No canonicality is assumed. -/
theorem values (logical : Slice U8) (out : alloc.vec.Vec U8) (bound : Nat)
    (small : logical.length≤bound) (room : out.length+bound≤Usize.max) :
    Post (fun pair => pair.2.length≤out.length+bound) (host_compact.compact_values logical out) := by
  by_cases h : logical.length%32=0
  · have len : logical.length=32*(logical.length/32) := by omega
    have hb := PV_RunJoin_CompactCompleteBound60.encode logical out (logical.length/32) len (by omega)
    cases he : host_compact.compact_values logical out with
    | fail e => trivial
    | div => trivial
    | ok pair =>
      rw [he] at hb
      change pair.2.length≤out.length+bound
      change pair.2.length≤out.length+16*(logical.length/32) at hb
      omega
  · rw [PV_RunJoin_CompactLengthReject40.reject logical out h]
    change out.length≤out.length+bound
    omega

/-- A total, unconditional bound for the actual claim plan projection. -/
theorem claim [ExternalTypes] [ExternalFuns] (p : prover.Publication) :
    Post (fun out => out.length≤Usize.max/2) (PV_RunJoin_ActualPlanSources59.compactClaim p) := by
  by_cases h : p.y1.length%32=0
  · have len : p.y1.length=32*(p.y1.length/32) := by omega
    have cap : p.y1.length≤Usize.max := p.y1.property
    have hb := PV_RunJoin_ClaimProjectionBound60.claim p (p.y1.length/32) len (by omega)
    cases he : PV_RunJoin_ActualPlanSources59.compactClaim p with
    | fail e => trivial
    | div => trivial
    | ok out =>
      rw [he] at hb
      change out.length≤Usize.max/2
      change out.length≤16*(p.y1.length/32) at hb
      omega
  · unfold PV_RunJoin_ActualPlanSources59.compactClaim
    rw [PV_RunJoin_CompactLengthReject40.reject (alloc.vec.Vec.deref p.y1) _ h]
    simp only [bind_tc_ok,Aeneas.Std.uncurry]
    change 0≤Usize.max/2
    omega

#print axioms values
#print axioms claim
end R1Z.PV_RunJoin_CompactUniversal62
