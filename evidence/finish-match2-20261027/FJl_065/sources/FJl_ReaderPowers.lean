import FJl_ReaderCanonical
import FJi_AllQueries
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_ReaderPowers
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- Canonical gamma is derived from THIS resumed reader; the SAME constructor
then supplies canonical selected powers and every coefficient value. -/
theorem value {Hash : Type} (base : VTop_Stages.Ops) (reserved : Bool)
    (D : VTop_Stages.aspis_core.digest.Digest32 Hash) (hash : Hash)
    (checkpoint proof pub : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
    (g : Array FIp_DotsAdapter.E 29#usize)
    (reader : Port4A_ReaderInstall.reader reserved D checkpoint proof pub .S2 hash=ok (.Ok (p,a)))
    (powers : Tx2N_Powers.powers 29#usize p.gamma=ok g) :
    FIo_ArrayCanon.Holds (FIp_DotsAdapter.toArray g) ∧
      ∀ j : Fin 29,FIp_ArrayValue.value (FIp_DotsAdapter.toArray g) j.val=
        CheckpointBytes5Output.ofE p.gamma^j.val := by
  have source := Port4A_ReaderInstall.accepted_source base reserved D hash checkpoint proof pub .S2 p a reader
  obtain ⟨fields⟩ := CheckpointBytes4Ops.successful_fields reserved (VTop_Checkpoint.digest D)
    checkpoint proof pub .S2 hash p a source
  have canonical := FJl_ReaderCanonical.read fields.rRoot1 fields.rGamma p.gamma fields.gammaRead
  exact FJi_SelectedPowers.value p.gamma g canonical powers
#print axioms value
end AspisR1.FJl_ReaderPowers
end
