import R1Z.ProverRwDictionaryScalar
import R1Z.ProverRwDictionaryLayoutSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryLayout
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryScalar.selected ops with
    op237 := .ok ProverRwDictionaryLayoutSource.compact.SLOT_NODES
    op241 := ProverRwDictionaryLayoutSource.compact.LOGICAL_SEMANTIC
    op242 := ProverRwDictionaryLayoutSource.compact.PROOF_BYTES
    op243 := ProverRwDictionaryLayoutSource.compact.OFF_NODES
    op244 := ProverRwDictionaryLayoutSource.compact.OFF_OPENINGS
    op245 := .ok ProverRwDictionaryLayoutSource.compact.MAGIC}

theorem entry237 (ops : ExternalFuns) : (selected ops).op237 = .ok ProverRwDictionaryLayoutSource.compact.SLOT_NODES := rfl

theorem entry241 (ops : ExternalFuns) : (selected ops).op241 = ProverRwDictionaryLayoutSource.compact.LOGICAL_SEMANTIC := rfl

theorem entry242 (ops : ExternalFuns) : (selected ops).op242 = ProverRwDictionaryLayoutSource.compact.PROOF_BYTES := rfl

theorem entry243 (ops : ExternalFuns) : (selected ops).op243 = ProverRwDictionaryLayoutSource.compact.OFF_NODES := rfl

theorem entry244 (ops : ExternalFuns) : (selected ops).op244 = ProverRwDictionaryLayoutSource.compact.OFF_OPENINGS := rfl

theorem entry245 (ops : ExternalFuns) : (selected ops).op245 = .ok ProverRwDictionaryLayoutSource.compact.MAGIC := rfl

#print axioms entry237
#print axioms entry241
#print axioms entry242
#print axioms entry243
#print axioms entry244
#print axioms entry245
end R1Z.ProverRwDictionaryLayout
