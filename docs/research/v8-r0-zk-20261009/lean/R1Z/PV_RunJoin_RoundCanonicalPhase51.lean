import R1Z.PV_RunJoin_RoundCanonicalStep51
import R1Z.PV_RunJoin_RoundThread38
import R1Z.PV_RunJoin_MergeLoop35
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundCanonicalPhase51
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_WeightInstalled46 PV_RunJoin_ResultPost41
open PV_RunJoin_PointPrefix51 (Prefix)
open PV_RunJoin_RoundCanonicalStep51 (Good Q)

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box) (ops : @ExternalFuns (types base))
    {H F : Type} (D : aspis_core.digest.Digest32 H) (oi : host_sumcheck.Oracle F) (oracle : F)
    (n : Nat) (round : Usize) (t : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (bound : round.val+n=10) (before : Prefix round.val point) :
    Post (Good 10) (@PV_RunJoin_RoundThread38.phase (types base) (selected base heap box ops)
      H F D oi n t out point running round oracle) := by
  letI : ExternalTypes := types base
  letI : ExternalFuns := selected base heap box ops
  induction n generalizing round t out point running with
  | zero =>
    simp only [PV_RunJoin_RoundThread38.phase,PV_RunJoin_RoundThread38.finish]
    apply PV_RunJoin_ResultPost41.bind
    intro result
    cases result with
    | Err e => trivial
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_ResultPost41.bind
      intro different
      cases different with
      | true => trivial
      | false =>
        have eq : round.val=10 := by omega
        rw [eq] at before
        exact before
  | succ n ih =>
    simp only [PV_RunJoin_RoundThread38.phase]
    have post := PV_RunJoin_RoundCanonicalStep51.complete base heap box ops D oi oracle round (by omega)
      t out point running before
    apply PV_RunJoin_RecordAppend41.bind_post post
    intro triple hp
    rcases triple with ⟨status,after,bytes⟩
    dsimp only [Aeneas.Std.uncurry]
    cases status with
    | Err e => trivial
    | Ok pair =>
      rcases pair with ⟨p,q⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift]
      have inc := PV_RunJoin_MergeLoop35.increment round (by omega)
      apply ih (Usize.wrapping_add round 1#usize) after bytes p q (by rw [inc];omega)
      rw [inc]
      exact hp
#print axioms complete
end R1Z.PV_RunJoin_RoundCanonicalPhase51
