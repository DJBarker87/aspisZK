import R1Z.PV_RunJoin_EntropyTotal

set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EntropyStep
open Aeneas Aeneas.Std Result ControlFlow ProverRwRng
open ProverRwRngOwnerDraw ProverRwRngOwnerEvents
variable [ErasureFns]

theorem afterFill_total (nonce : Array U8 32#usize) (retry : Usize)
    (below : retry < 16#usize)
    (reply : (Tape × core.result.Result Unit U8) × Array U8 64#usize) :
    ∃ flow, afterFill nonce retry reply = .ok flow := by
  rcases reply with ⟨⟨after,status⟩,block⟩
  cases status with
  | Err error => exact ⟨.done (after,.Err (.Os error)),rfl⟩
  | Ok returnedUnit =>
    have spec : afterFill nonce retry ((after,.Ok returnedUnit),block) ⦃ _ => True ⦄ := by
      unfold afterFill
      simp only [zeroize.Zeroizing.new,zeroize.Zeroizing.Insts.CoreOpsDerefDerefMut.deref_mut,
        zeroize.Zeroizing.Insts.CoreOpsDerefDeref.deref,bind_tc_ok,Aeneas.Std.uncurry]
      step <;> try scalar_tac
      step <;> try scalar_tac
      step <;> try scalar_tac
      step <;> try scalar_tac
      step <;> try scalar_tac
      step <;> try scalar_tac
      obtain ⟨first,firstRun⟩ := PV_RunJoin_EntropyTotal.nonzero_total _
      rw [firstRun]
      simp only [bind_tc_ok]
      split
      · obtain ⟨second,secondRun⟩ := PV_RunJoin_EntropyTotal.nonzero_total _
        rw [secondRun]
        simp only [bind_tc_ok]
        split
        · simp only [WP.spec_ok]
        · step <;> try scalar_tac
      · step <;> try scalar_tac
    obtain ⟨flow,run,_⟩ := WP.spec_imp_exists spec
    exact ⟨flow,run⟩

#print axioms afterFill_total
end R1Z.PV_RunJoin_EntropyStep
