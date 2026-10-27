import R1Z.ProverRwFullFuns
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RE_Prefix001
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
variable [ExternalTypes] [ExternalFuns]

/-- Exact first bind of `aspis_prover.state_only_entropy.Profile21SourceExpander.new` (op128).
This is a source prefix certificate, not a witness that a fixture enters it. -/
theorem first
  (hash : Slice (Slice Std.U8) → Result (Array Std.U8 32#usize)) (seed : Array Std.U8 32#usize) :
  ∃ next, @aspis_prover.state_only_entropy.Profile21SourceExpander.new _ _ hash seed =
    (zeroize.Zeroizing.new (Array.Insts.ZeroizeZeroize 32#usize
      (zeroize.Zeroize.Blanket U8.Insts.ZeroizeDefaultIsZeroes)) seed >>= next) := by
  unfold aspis_prover.state_only_entropy.Profile21SourceExpander.new
  exact ⟨_,rfl⟩

#print axioms first
end R1Z.PV_RE_Prefix001
