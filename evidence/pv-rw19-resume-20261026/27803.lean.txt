import R1Z.ProverRw19ByteLength
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19PublishLength
open Aeneas Aeneas.Std Result ProverRwFull ProverRw19ByteLength
variable [ExternalTypes] [ExternalFuns]

-- The final emitted massert proves the returned length. Earlier codecs and
-- opening/node loops remain arbitrary Results, never concretely unrolled.
theorem publish (variant : transport.Variant) (publication : prover.Publication)
    (size : Usize) (P_proof_size : compact.PROOF_BYTES = ok size) :
    HasLength size.val (prover.publish_compact variant publication) := by
  unfold prover.publish_compact
  rw [P_proof_size]
  simp only [bind_tc_ok]
  repeat' first
    | exact residual _ _
    | apply guarded; intro h
    | apply successful _ size; assumption
    | apply bind_good; intro x
    | dsimp only [Aeneas.Std.uncurry]
    | split

#print axioms publish
end R1Z.ProverRw19PublishLength
