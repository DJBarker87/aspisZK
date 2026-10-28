import R1Z.ProverRw18ContextTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18ContextJoin
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw18InlineContext
variable [ExternalTypes]
abbrev Compression := U32 → Slice U32 → Q → Result Q

-- The source-law argument belongs to pv-cb3/op223. This theorem neither
-- defines a purported original-source extraction nor proves that argument.
-- The independent identity obligation names the exact context checked here.
theorem callback (ops : ExternalFuns) (extracted : Compression)
    (source_law : ops.op223=extracted)
    (context_identity : extracted =
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)) :
    ops.op223=PV_RW_CompressClosed.owned := by
  rw [source_law,context_identity]
  funext tag values lambda
  exact ProverRw18ContextCompression.owned ops tag values lambda

-- These are auxiliary dictionaries until source_law and context_identity are
-- supplied for the live source interpretation. No callback row is removed.
def original (ops : ExternalFuns) : ExternalFuns :=
  {PV_CurrentScaleInstall.selected ops with op223 := ops.op223}

def owned (ops : ExternalFuns) : ExternalFuns :=
  {PV_CurrentScaleInstall.selected ops with op223 := PV_RW_CompressClosed.owned}

theorem dictionaries (ops : ExternalFuns) (extracted : Compression)
    (source_law : ops.op223=extracted)
    (context_identity : extracted =
      @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)) :
    original ops=owned ops := by
  unfold original owned
  rw [callback ops extracted source_law context_identity]

#print axioms callback
#print axioms dictionaries
end R1Z.ProverRw18ContextJoin
