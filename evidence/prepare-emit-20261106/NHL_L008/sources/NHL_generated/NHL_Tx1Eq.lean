import NHL_EmittedTx1
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_Tx1Eq
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
/-- The complete fresh tx1 emission equals the adopted enclosing tx1 body.
This installs its actual prepare call; it assumes no tx1 output/success. -/
theorem source (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 NHL_EmittedTx1.tx1 ops (verifier.candidate.prepare ops) D pub public_bytes proof k hash obs=
 verifier.candidate.tx1 ops D pub public_bytes proof k hash obs := by rfl
#print axioms source
end AspisR1.NHL_Tx1Eq
