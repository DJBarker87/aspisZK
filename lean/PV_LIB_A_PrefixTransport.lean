import PV_THR2_InterpreterAgreement
set_option autoImplicit false
namespace PV_LIB_A_PrefixTransport
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
/-- Reuse the provider's ONE symbolic induction at a finite delivery cutoff.
Unlike the old f6 helper, this needs no agreement after that cutoff. The caller
must identify its own delivery and discharge table/handler agreement on the
actual prefixes from emitted bodies and named leaf semantics. -/
theorem prefix_identity {W E : Type} (B : Carrier W Data) (K : Control)
    (leftP rightP : Data → Option PV_STX2_SliceSyntax.Program)
    (leftH rightH : PV_STX2_Native.Request Data → W → Reply W E Data)
    (boundary : Nat) (q : PV_THR2_IntrinsicState.State W E)
    (same : ∀ k, k < boundary →
      PV_THR2_TableIntrinsic.Agree leftP rightP
        (PV_THR2_IntrinsicState.advance B K leftP leftH k q) ∧
      PV_THR2_InterpreterAgreement.NativeAgree leftH rightH
        (PV_THR2_IntrinsicState.advance B K leftP leftH k q)) :
    ∀ n, n ≤ boundary →
      PV_THR2_IntrinsicState.advance B K leftP leftH n q =
        PV_THR2_IntrinsicState.advance B K rightP rightH n q := by
  intro n bounded
  exact (PV_THR2_InterpreterAgreement.run B K leftP rightP leftH rightH n q
    (fun k hk => same k (Nat.lt_of_lt_of_le hk bounded))).symm
#print axioms prefix_identity
end PV_LIB_A_PrefixTransport
