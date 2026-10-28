import R1Z.PV_RunJoin_RoundStream43
import R1Z.PV_RunJoin_RoundThread38
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RoundAccum43
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_ResultPost41
open PV_RunJoin_RoundStream43
variable [ExternalTypes]
abbrev Q := aspis_core.field.QM31

def Good {H : Type} (out : alloc.vec.Vec U8) (n : Nat)
    (next : (core.result.Result (Array Q 10#usize × Q) r1_wire.Error) ×
      host_wire.SemanticTranscript H × alloc.vec.Vec U8) : Prop :=
  match next.1 with
  | .Ok _ => Stream out.val n next.2.2.val
  | .Err _ => True

theorem phase (ops : ExternalFuns) {H F : Type} (hash : aspis_core.digest.Digest32 H)
    (oi : host_sumcheck.Oracle F) (oracle : F) (n : Nat) (round : Usize)
    (transcript : host_wire.SemanticTranscript H) (out : alloc.vec.Vec U8)
    (point : Array Q 10#usize) (running : Q) (bound : round.val+n=10)
    (room : out.length+901*n≤Usize.max) :
    Post (Good out n) (@PV_RunJoin_RoundThread38.phase _ (ProverRwP6BodyCandidate.selected ops)
      H F hash oi n transcript out point running round oracle) := by
  letI : ExternalFuns := ProverRwP6BodyCandidate.selected ops
  induction n generalizing round transcript out point running with
  | zero =>
    simp only [PV_RunJoin_RoundThread38.phase,PV_RunJoin_RoundThread38.finish]
    apply PV_RunJoin_ResultPost41.bind
    intro r
    cases r with
    | Err e => trivial
    | Ok value =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
      apply PV_RunJoin_ResultPost41.bind
      intro different
      cases different with
      | true => trivial
      | false => exact Stream.nil out.val
  | succ n ih =>
    simp only [PV_RunJoin_RoundThread38.phase]
    change out.val.length+901*(n+1)≤Usize.max at room
    have stepRoom : out.length+901≤Usize.max := by
      change out.val.length+901≤Usize.max
      apply Nat.le_trans _ room
      apply Nat.add_le_add_left
      have h := Nat.mul_le_mul_left 901 (Nat.succ_le_succ (Nat.zero_le n))
      simpa only [Nat.mul_one] using h
    have post := PV_RunJoin_RoundRecord43.post ops hash oi oracle round (by omega)
      transcript out point running stepRoom
    apply PV_RunJoin_RecordAppend41.bind_post post
    intro triple hp
    rcases triple with ⟨r,t,o⟩
    dsimp only [Aeneas.Std.uncurry]
    cases r with
    | Err e => trivial
    | Ok pair =>
      rcases pair with ⟨p,q⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,lift]
      have inc := PV_RunJoin_MergeLoop35.increment round (by omega)
      have olen := PV_RunJoin_RoundStream43.added_length hp
      have next := ih (Usize.wrapping_add round 1#usize) t o p q
        (by rw [inc];omega) (by change o.val.length+901*n≤Usize.max;rw [olen];omega)
      apply PV_RunJoin_PostMap43.mono next
      intro result hr
      rcases result with ⟨status,t1,o1⟩
      cases status with
      | Err e => trivial
      | Ok value => exact Stream.cons hp hr

#print axioms phase
end R1Z.PV_RunJoin_RoundAccum43
