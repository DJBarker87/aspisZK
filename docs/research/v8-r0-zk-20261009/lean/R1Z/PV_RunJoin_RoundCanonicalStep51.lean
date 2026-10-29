import R1Z.PV_RunJoin_PointPrefix51
import R1Z.PV_RunJoin_SemanticCanonicalPost51
import R1Z.PV_RunJoin_RecordAppend41
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundCanonicalStep51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
open PV_RunJoin_PointPrefix51 (Prefix)
abbrev Q := ProverRwFull.aspis_core.field.QM31

def Good {H : Type} (n : Nat) (triple :
    core.result.Result (Array Q 10#usize × Q) r1_wire.Error × host_wire.SemanticTranscript H × alloc.vec.Vec U8) : Prop :=
  match triple.1 with
  | .Err _ => True
  | .Ok pair => Prefix n pair.1

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H F : Type} (D : aspis_core.digest.Digest32 H) (oi : host_sumcheck.Oracle F) (oracle : F)
    (round : Usize) (small : round.val<10) (t : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (before : Prefix round.val point) :
    Post (Good (round.val+1)) (@host_sumcheck.prove_sumcheck_round (types base) (selected base heap box ops)
      H F D oi t out point running round oracle) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  unfold host_sumcheck.prove_sumcheck_round
  simp only [lift,bind_tc_ok]
  apply PV_RunJoin_ResultPost41.bind
  intro zero
  apply PV_RunJoin_ResultPost41.bind
  intro evaluations
  apply PV_RunJoin_ResultPost41.bind
  intro merged
  cases merged with
  | Err e => trivial
  | Ok values =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,Aeneas.Std.uncurry,bind_assoc_eq]
    apply PV_RunJoin_ResultPost41.bind
    intro polynomial
    apply PV_RunJoin_ResultPost41.bind
    intro boundary
    apply PV_RunJoin_ResultPost41.bind
    intro different
    cases different with
    | true => trivial
    | false =>
      simp only [Bool.false_eq_true,if_false]
      apply PV_RunJoin_ResultPost41.bind
      intro bytes
      apply PV_RunJoin_ResultPost41.bind
      intro recorded
      cases recorded with
      | Err e => trivial
      | Ok framed =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift]
        have post := PV_RunJoin_SemanticCanonicalPost51.complete base heap box ops D t
          (U8.wrapping_add 15#u8 (UScalar.cast .U8 round)) (alloc.vec.Vec.deref framed)
        apply PV_RunJoin_RecordAppend41.bind_post post
        intro pair canonical
        rcases pair with ⟨status,nextTranscript⟩
        dsimp only [Aeneas.Std.uncurry]
        cases status with
        | Err e => trivial
        | Ok q =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
          obtain ⟨next,hn,hprefix⟩ := PV_RunJoin_PointPrefix51.update point round q small before canonical
          rw [hn]
          simp only [bind_tc_ok,lift]
          apply PV_RunJoin_ResultPost41.bind
          intro nextOutput
          apply PV_RunJoin_ResultPost41.bind
          intro readPoint
          apply PV_RunJoin_ResultPost41.bind
          intro nextRunning
          exact hprefix
#print axioms Good
#print axioms complete
end R1Z.PV_RunJoin_RoundCanonicalStep51
