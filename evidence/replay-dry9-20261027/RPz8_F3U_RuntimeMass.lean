import RPz8_F3U_RuntimePointwise
import RPz8_F3U_Averaging
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_RuntimeMass
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.CausalFirstHitUnionBound
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_Carried F3T_Runtime
open RawRecordedOracleExtractionMassBin F3U_CollisionJoin

theorem charge {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : F3T_CanonicalJoin.Physical rust)
    (bad : Exception) (join : Join c D rust bad) (P : ByteProver) (runtime : Runtime)
    (binding : StoredCarrierBinding c D rust P runtime)
    (account : Program Bytes State A) (event : View Bytes State A → Prop)
    (association : ∀ H : Bytes → State,bad H (eval H P).2.publicBytes (eval H P).2.stored → event (eval H account)) :
    deployedFailure runtime≤lazyMean (projected D (F3T_Canon.canon (lift c P))) emptyTable failureMass+
      lazyMean account emptyTable (fun v=>indicator (event v)) := by
  apply F3U_Averaging.charge
  intro H
  exact (F3U_RuntimePointwise.charge c D rust physical bad join P runtime binding H).trans
    (add_le_add (le_refl _) (indicator_mono (association H)))

#print axioms charge
end AspisR1.F3U_RuntimeMass
end
