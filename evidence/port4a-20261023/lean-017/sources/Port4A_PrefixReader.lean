import Port4A_ReaderInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_PrefixReader
open Aeneas Aeneas.Std Result VTop_Stages

/-- Replacing only the reader cannot change a TX1 prefix. Prove this before
instantiating a large dictionary, to avoid kernel unfolding all native loops. -/
theorem prefix_iff (base : Ops) (reserved : Bool) {H : Type}
    (D : aspis_core.digest.Digest32 H) (hash : H)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (split : Usize) (p : verifier.Prepared) (a : verifier.Accumulator) :
    VTop_Provenance.WriterPrefix (Port4A_ReaderInstall.install base reserved)
      D hash semantic proof split none p a ↔
    VTop_Provenance.WriterPrefix base D hash semantic proof split none p a := by rfl

#print axioms prefix_iff
end AspisR1.Port4A_PrefixReader
end
