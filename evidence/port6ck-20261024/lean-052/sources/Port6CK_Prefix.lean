import Port6CK_Reader
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_Prefix
open Aeneas Aeneas.Std Result VTop_Stages
open Port6CK_Semantic (Unwrap)

theorem same (base : Ops) (reserved : Bool) (unwrap : Unwrap) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator) :
    VTop_Provenance.WriterPrefix (Port6CK_Reader.install base reserved unwrap)
      D hash semantic proof split none p a ↔
    VTop_Provenance.WriterPrefix base D hash semantic proof split none p a := by rfl

#print axioms same
end AspisR1.Port6CK_Prefix
end
