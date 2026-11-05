import NIS_DigestCarrier
set_option autoImplicit false
noncomputable section
namespace NIS_Tx1Release
open Aeneas Aeneas.Std Result

/-- Release-only interface preflight after the explicit Digest32 carrier.
No slot is installed and no native/accepted outcome is assumed. -/
def release {H : Type} (base : AspisR1CurrentCaller.Ops)
    (first : AspisR1.NHL_EmittedTx1.Prepare H)
    (D : AdapterRw.aspis_core.digest.Digest32 H)
    (pub : AdapterRw.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (public_bytes proof : Slice U8) (k : Usize) (hash : H) :
    Result (core.result.Result (alloc.vec.Vec U8) AdapterRw.aspis_r1_cost_probe.verifier.Error) :=
  AspisR1.NHL_EmittedTx1.tx1 base first (NIS_DigestCarrier.toCaller D)
    pub public_bytes proof k hash none

#print axioms release
end NIS_Tx1Release
