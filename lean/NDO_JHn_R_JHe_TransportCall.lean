import NDO_JHn_R_JHe_WriterCommutation
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHe_TransportCall
open Aeneas Aeneas.Std Result AspisR1CurrentCaller

theorem source {H : Type} (left right : Ops)
    (D E : aspis_core.digest.Digest32 H) (operations : left=right) (dictionary : D=E)
    (hash : H) (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 right E semantic pub proof split hash none=ok (.Ok saved)) :
    verifier.candidate.tx1 left D semantic pub proof split hash none=ok (.Ok saved) := by
  cases operations
  cases dictionary
  exact accepted
#print axioms source
end AspisR1.JHe_TransportCall
end
