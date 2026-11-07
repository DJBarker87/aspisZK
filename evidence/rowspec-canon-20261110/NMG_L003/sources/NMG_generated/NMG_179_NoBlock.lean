import NGT_NBL_BlockTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMG_179_NoBlock
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
/-- A Block contains successful runtime replies. Widths alone cannot produce
one for every arbitrary digest. This is a model counterexample only. -/
theorem no_block {H : Type} (D : aspis_core.Digest32 H)
 (before : transcript.Transcript H) (row : U8) (payload : Slice U8)
 (rejects : ∀ parts, D.digest before.hash parts=.fail .panic) :
 ¬ Nonempty (NGT_NBL_BlockTrace.Block D before row payload) := by
 intro ⟨block⟩
 have failed := rejects (NGT_NBA_Transcript.absorbParts before.state block.tag payload)
 rw [block.absorbCall] at failed
 cases failed
#print axioms no_block
end AspisR1.NMG_179_NoBlock
end
