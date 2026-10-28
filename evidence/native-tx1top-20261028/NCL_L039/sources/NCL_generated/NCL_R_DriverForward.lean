import RPx_Deployed
import NCL_R_DriverCuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCL_DriverForward
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
attribute [local irreducible] verifier.candidate.prepare

/-- Replay the emitted outer driver on the SAME proof/public/hash and the
same carriers in source order. All observations are local child statements;
none is a second whole-driver acceptance premise. -/
theorem source (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (hash : H) (saved : alloc.vec.Vec U8)
    (start : compact.OFF_FOLDED_ROOT ops = ok 7751#usize)
    (finish : compact.OFF_ROUND1 ops = ok 7783#usize)
    (c : NCL_DriverCuts.Cuts ops D semantic pub proof hash saved) :
    verifier.candidate.tx1 ops D semantic pub proof 10#usize hash none = ok (.Ok saved) := by
  with_reducible
    simp only [verifier.candidate.tx1,compact.SPLIT,bne_self_eq_false,Bool.false_eq_true,
      if_false,c.shape,c.scan,c.zero_call,c.prepare,c.initial_call,start,finish,
      c.root_range,c.root_copy,c.batch,c.geometry_call,c.pending_call,c.query,
      c.flush,c.checkpoint,verifier.mark,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch,core.result.Result.unwrap,
      alloc.vec.Vec.deref_mut,lift,Aeneas.Std.uncurry]
  change (do let values ← ops.op17 c.after c.out.weights.deref
             let bytes ← ops.op16 D c.prepared
               {c.out with weights := ⟨values.val,values.property⟩} proof pub hash
             ok (core.result.Result.Ok (E := verifier.Error) bytes)) = ok (core.result.Result.Ok (E := verifier.Error) saved)
  rw [c.flush]
  simp only [bind_tc_ok,c.checkpoint]
#print axioms source
end AspisR1.NCL_DriverForward
end
