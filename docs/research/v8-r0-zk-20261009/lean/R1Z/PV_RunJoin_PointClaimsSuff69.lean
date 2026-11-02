import R1Z.PV_RunJoin_ClaimsLoop69
set_option autoImplicit false
namespace R1Z.PV_RunJoin_PointClaimsSuff69
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes] [ExternalFuns]
abbrev Q := aspis_core.field.QM31

theorem claims
    (some_ok : ∀ q : Q,core.option.Option.ok_or (some q) r1_wire.Error.Public=ok (.Ok q))
    (zero : ∃ z,aspis_core.field.QM31.ZERO=ok z)
    (columns : Array (alloc.vec.Vec Q) 29#usize) (point : Array Q 10#usize)
    (evaluates : ∀ (lane : Usize) (v : alloc.vec.Vec Q), lane.val<29 →
      Array.index_usize columns lane=ok v →
      ∃ q,aspis_statement.constraints_v4.multilinear_evaluate_qm31 (alloc.vec.Vec.deref v) point=ok (some q)) :
    ∃ out,host_semantic.claims_at_point columns point=ok (.Ok out) := by
  obtain ⟨z,hz⟩ := zero
  obtain ⟨out,ho⟩ := PV_RunJoin_ClaimsLoop69.complete some_ok columns point evaluates
    29 0#usize (Array.repeat 29#usize z) rfl
  exact ⟨out,by simp only [host_semantic.claims_at_point,hz,ho,bind_tc_ok,Aeneas.Std.uncurry]⟩

/-- All three statement points are the actual source-selected points. -/
theorem complete
    (some_ok : ∀ q : Q,core.option.Option.ok_or (some q) r1_wire.Error.Public=ok (.Ok q))
    (zero : ∃ z,aspis_core.field.QM31.ZERO=ok z)
    (columns : Array (alloc.vec.Vec Q) 29#usize) (point : Array Q 10#usize)
    (points : Array (Array Q 10#usize) 3#usize)
    (hp : r1_wire.statement_points point=ok points)
    (evaluates : ∀ (p : Array Q 10#usize) (lane : Usize) (v : alloc.vec.Vec Q),
      lane.val<29 → Array.index_usize columns lane=ok v →
      ∃ q,aspis_statement.constraints_v4.multilinear_evaluate_qm31 (alloc.vec.Vec.deref v) p=ok (some q)) :
    ∃ out,host_semantic.point_claims columns point=ok (.Ok out) := by
  obtain ⟨p0,h0⟩ := ProverRwP6ArrayRead.read points 0#usize (by decide)
  obtain ⟨p1,h1⟩ := ProverRwP6ArrayRead.read points 1#usize (by decide)
  obtain ⟨p2,h2⟩ := ProverRwP6ArrayRead.read points 2#usize (by decide)
  obtain ⟨c0,hc0⟩ := claims some_ok zero columns p0 (evaluates p0)
  obtain ⟨c1,hc1⟩ := claims some_ok zero columns p1 (evaluates p1)
  obtain ⟨c2,hc2⟩ := claims some_ok zero columns p2 (evaluates p2)
  exact ⟨Array.make 3#usize [c0,c1,c2],by simp only [host_semantic.point_claims,hp,h0,h1,h2,hc0,hc1,hc2,
    core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]⟩

#print axioms claims
#print axioms complete
end R1Z.PV_RunJoin_PointClaimsSuff69
