import R1Z.PV_Canon_Prefix
import R1Z.PV_Canon_CheckedRound
import R1Z.PV_Canon_BindCongr
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
/-- Instrumentation of the actual extracted one-round caller; proving this
removes the canonical-domain guard from that body's only op121 call. -/
theorem round_checked (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    {H F : Type} (digest : aspis_core.digest.Digest32 H) (oracleInst : host_sumcheck.Oracle F)
    (s : host_wire.SemanticTranscript H) (output : alloc.vec.Vec U8)
    (point : Array aspis_core.field.QM31 10#usize) (running : aspis_core.field.QM31)
    (round : Usize) (oracle : F) (hr : round.val < 10) :
    @host_sumcheck.prove_sumcheck_round (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) H F digest oracleInst s output point running round oracle =
    @checked_round (PV_Join_PublicCaller.native base)
      (PV_Join_PublicCaller.selected base ops) H F digest oracleInst s output point running round oracle := by
  letI : ExternalTypes := PV_Join_PublicCaller.native base
  letI : ExternalFuns := PV_Join_PublicCaller.selected base ops
  unfold host_sumcheck.prove_sumcheck_round checked_round
  apply bind_congr_all; intro remaining
  apply bind_congr_all; intro zero
  apply bind_congr_all; intro assignments
  apply bind_congr_all; intro tag
  apply bind_congr_all; intro count
  apply bind_congr_all; intro evaluations
  apply bind_congr_all; intro merged
  apply bind_congr_all; intro branch
  cases branch with
  | Break residual => rfl
  | Continue values =>
    apply bind_congr_success; intro coefficients hp
    have hc := polynomial base ops values coefficients hp
    apply bind_congr_all; intro boundary
    apply bind_congr_all; intro mismatch
    split
    · rfl
    · apply bind_congr_all; intro encoded
      apply bind_congr_all; intro tagCast
      apply bind_congr_all; intro tagAdd
      apply bind_congr_all; intro record
      apply bind_congr_all; intro branch
      cases branch with
      | Break residual => rfl
      | Continue framed =>
        apply bind_congr_all; intro tagCast2
        apply bind_congr_all; intro tagAdd2
        apply bind_congr_success; rintro ⟨sem,after⟩ hs
        cases sem with
        | Err e => rfl
        | Ok sampled =>
          change (do
            let point1 ← Array.update point round sampled
            let output1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 output (alloc.vec.Vec.deref framed)
            let read ← Array.index_usize point1 round
            let value ← aspis_core.state_only_sumcheck.evaluate_state_only_polynomial coefficients read
            ok (core.result.Result.Ok (point1,value),after,output1)) = (do
            let point1 ← Array.update point round sampled
            let output1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 output (alloc.vec.Vec.deref framed)
            let read ← Array.index_usize point1 round
            let value ← checked_eval coefficients read
            ok (core.result.Result.Ok (point1,value),after,output1))
          apply bind_congr_success; intro updated hu
          apply bind_congr_all; intro extended
          apply bind_congr_success; intro read hi
          have hq := update_read_canonical point updated round sampled read hr
            (current_semantic base ops digest s after tagAdd2 (alloc.vec.Vec.deref framed) sampled hs) hu hi
          rw [checked_eval_eq coefficients read hc hq]
#print axioms round_checked
end R1Z.PV_Canon
