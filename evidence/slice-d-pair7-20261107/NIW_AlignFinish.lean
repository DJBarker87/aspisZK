import NIT_Cuts
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinish
open Aeneas Aeneas.Std Result NIT_Cuts AspisR1Stage2

/-- The returning NEW cut constrains the address but does not constrain the
returned decoded payload. This replacement preserves every asserted fact. -/
theorem new_payload_free (p : verifier.Prepared) (alpha z owner : Nat)
 (before after : NewPort) (out : Ref FIo_Install.W) (replacement : FIo_Install.W)
 (cut : cutNewPort p alpha z owner before after (.Ok out)) :
 cutNewPort p alpha z owner before after (.Ok {out with value:=replacement}) := by
 exact cut

theorem new_payload_not_determined (p : verifier.Prepared) (alpha z owner : Nat)
 (before after : NewPort) (out : Ref FIo_Install.W) (replacement : FIo_Install.W)
 (cut : cutNewPort p alpha z owner before after (.Ok out))
 (different : replacement ≠ out.value) :
 ∃ other : Ref FIo_Install.W,
 cutNewPort p alpha z owner before after (.Ok other) ∧
 other.address=out.address ∧ other.value≠out.value := by
 exact ⟨{out with value:=replacement},new_payload_free p alpha z owner before after out replacement cut,rfl,different⟩

/-- Entered NEW is conditional on both earlier rounds returning successfully;
the first round's value is not replaced by a selected witness. -/
theorem new_reached (a : verifier.Accumulator) (l : FinishLog)
 (reached : 3 ≤ (finishExpected a l).2) :
 ∃ first claim, l.round_reply 0=.Ok first ∧ l.round_reply 1=.Ok claim := by
 cases h0 : l.round_reply 0 with
 | Err e => simp [finishExpected,h0] at reached
 | Ok first =>
  cases h1 : l.round_reply 1 with
  | Err e => simp [finishExpected,h0,h1] at reached
  | Ok claim => exact ⟨first,claim,rfl,rfl⟩

theorem pair_reached (a : verifier.Accumulator) (l : FinishLog)
 (reached : 4 ≤ (finishExpected a l).2) :
 (∃ first claim,l.round_reply 0=.Ok first ∧ l.round_reply 1=.Ok claim) ∧
 l.new.error=none := by
 obtain ⟨first,claim,h0,h1⟩ := new_reached a l (by omega)
 cases hn : l.new.error with
 | some e => simp [finishExpected,h0,h1,hn] at reached
 | none => exact ⟨⟨first,claim,h0,h1⟩,rfl⟩

/-- Dot can be entered only after the actual pair Result returned the same
field value as round1. No successful-child premise is added. -/
theorem dot_reached (a : verifier.Accumulator) (l : FinishLog)
 (reached : 6 ≤ (finishExpected a l).2) :
 ∃ first claim,l.round_reply 0=.Ok first ∧ l.round_reply 1=.Ok claim ∧
 l.new.error=none ∧ l.pair.reply=.Ok claim := by
 obtain ⟨⟨first,claim,h0,h1⟩,hn⟩ := pair_reached a l (by omega)
 cases hp : l.pair.reply with
 | Err e => simp [finishExpected,h0,h1,hn,hp] at reached
 | Ok pair =>
  by_cases he : pair=claim
  · subst pair; exact ⟨first,claim,h0,h1,hn,rfl⟩
  · simp [finishExpected,h0,h1,hn,hp,he] at reached

#print axioms new_payload_free
#print axioms new_payload_not_determined
#print axioms new_reached
#print axioms pair_reached
#print axioms dot_reached
end AspisR1.NIW_AlignFinish
