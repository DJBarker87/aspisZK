import R1Z.PV_RunJoin_SliceBound62
import R1Z.PV_RunJoin_CompactUniversal62
set_option autoImplicit false
namespace R1Z.PV_RunJoin_SemanticRowBound62
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
variable [ExternalTypes] [ExternalFuns]

theorem row (logical : Slice U8) (out : alloc.vec.Vec U8) (row : U8) (at1 : Usize)
    (bound : Nat) (small : logical.length≤bound) (room : out.length+2*bound≤Usize.max) :
    Post (fun pair => pair.2.length≤out.length+2*bound)
      (host_compact.compact_semantic_row logical out row at1) := by
  unfold host_compact.compact_semantic_row
  apply PV_RunJoin_ResultPost41.bind
  intro shape
  apply PV_RunJoin_ResultPost41.bind
  intro status
  cases status with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
    apply PV_RunJoin_ResultPost41.bind
    intro ignored
    change out.length≤out.length+2*bound
    omega
  | Ok value =>
    rcases value with ⟨tag,size⟩
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift]
    apply PV_RunJoin_PostBind62.bind _ _ _ _ (PV_RunJoin_SliceBound62.range logical at1 _)
    intro head headBound
    apply PV_RunJoin_PostBind62.bind _ _ _ _ (PV_RunJoin_SliceBound62.append out head)
    intro mid midLength
    apply PV_RunJoin_ResultPost41.bind
    intro compressed
    cases compressed with
    | false =>
      simp only [Bool.false_eq_true,if_false,lift,bind_tc_ok]
      apply PV_RunJoin_PostBind62.bind _ _ _ _ (PV_RunJoin_SliceBound62.range logical _ _)
      intro payload payloadBound
      apply PV_RunJoin_PostBind62.bind _ _ _ _ (PV_RunJoin_SliceBound62.append mid payload)
      intro next nextLength
      simp only [lift,bind_tc_ok]
      change next.length≤out.length+2*bound
      omega
    | true =>
      simp only [if_true,lift,bind_tc_ok]
      apply PV_RunJoin_PostBind62.bind _ _ _ _ (PV_RunJoin_SliceBound62.range logical _ _)
      intro payload payloadBound
      apply PV_RunJoin_PostBind62.bind _ _ _ _
        (PV_RunJoin_CompactUniversal62.values payload mid bound (by omega) (by omega))
      rintro ⟨codecStatus,next⟩ nextBound
      dsimp only [Aeneas.Std.uncurry]
      cases codecStatus with
      | Err e =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
        apply PV_RunJoin_ResultPost41.bind
        intro ignored
        change next.length≤out.length+2*bound
        omega
      | Ok u =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,lift,bind_tc_ok]
        change next.length≤out.length+2*bound
        omega

#print axioms row
end R1Z.PV_RunJoin_SemanticRowBound62
