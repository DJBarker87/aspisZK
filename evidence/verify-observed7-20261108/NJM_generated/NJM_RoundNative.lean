import NJM_RoundContinuation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJM_RoundNative
open Aeneas Aeneas.Std Result AspisR1PublicPreparation NIX_CertificateFrames
attribute [local instance] Classical.propDecidable

/-- The SAME native post windows assemble exactly the source active-slot write. -/
theorem alpha (s : RoundPre) (q : Q) (bound : s.round.val<10)
 (semantic : s.semantic=.Ok q) : NJG_RoundResult.alpha s=s.alpha.set s.round q := by
 apply array_ext
 intro j
 rw [NJG_RoundResult.alpha_cell]
 simp only [alphaCell,semantic]
 by_cases eq : j.val=s.round.val
 · simp [eq,cell,FJb_TailCell.cell,Aeneas.Std.Array.set]
 · simp [eq,cell,FJb_TailCell.cell,Aeneas.Std.Array.set,Ne.symm eq]

/-- Decoder rejection consumes the SAME all-window native cut. -/
theorem rejected (s : RoundPre) (post : RoundOutput) (e : r1_wire.Error)
 (decoder : s.polynomial=.Err e) (cut : ∀ j z,roundResult s j z post) : post=.Err e := by
 rw [NJG_RoundResult.complete s post cut]
 simp only [NJG_RoundResult.reply,decoder]

/-- Boundary rejection has no semantic/value suffix. -/
theorem boundary (s : RoundPre) (post : RoundOutput) (p : Polynomial)
 (decoder : s.polynomial=.Ok p) (different : s.boundary≠s.running)
 (cut : ∀ j z,roundResult s j z post) : post=.Err (.Boundary s.round) := by
 rw [NJG_RoundResult.complete s post cut]
 simp only [NJG_RoundResult.reply,decoder,if_pos different]

/-- Semantic rejection preserves its full Error constructor and fields. -/
theorem semantic_error (s : RoundPre) (post : RoundOutput) (p : Polynomial) (e : r1_wire.Error)
 (decoder : s.polynomial=.Ok p) (same : s.boundary=s.running) (semantic : s.semantic=.Err e)
 (cut : ∀ j z,roundResult s j z post) : post=.Err e := by
 rw [NJG_RoundResult.complete s post cut]
 simp only [NJG_RoundResult.reply,decoder,if_neg (not_not.mpr same),semantic]

/-- Success consumes every SAME post window; no array is independently chosen. -/
theorem success (s : RoundPre) (post : RoundOutput) (p : Polynomial) (q : Q)
 (decoder : s.polynomial=.Ok p) (same : s.boundary=s.running) (semantic : s.semantic=.Ok q)
 (bound : s.round.val<10) (cut : ∀ j z,roundResult s j z post) :
 post=.Ok (s.value,s.alpha.set s.round q,s.newState,s.newNext) := by
 rw [NJG_RoundResult.complete s post cut]
 simp only [NJG_RoundResult.reply,decoder,if_neg (not_not.mpr same),semantic,alpha s q bound semantic]

#print axioms alpha
#print axioms rejected
#print axioms boundary
#print axioms semantic_error
#print axioms success
end AspisR1.NJM_RoundNative
end
