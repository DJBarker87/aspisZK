import ART_StartCharge
set_option autoImplicit false
noncomputable section
namespace AspisR1.ART_StartPrefix
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.AdaptiveFirstReadLaw
open FS FS2
open SCE_Experiment F3T_Experiment F3T_ByteCarrier

theorem original_index {A F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (a : Adversary A) (H : Bytes → State) (address : Bytes)
    (read : Read (eval H (F3T_Charged.charged D (F3T_Canon.canon (lift c (submission a))))).1 address) :
    firstIdx address (eval H (F3T_Charged.projected D (F3T_Canon.canon (lift c (submission a))))).1 =
    firstIdx address (eval H (F3T_Charged.charged D (F3T_Canon.canon (lift c (submission a))))).1 :=
  F3T_Prefix.first_start_before_terminal D _ H address read

/-- The frozen2 predecessor uses the identical prefix/first-occurrence rule;
this is why the 34 allowance is per transcript, not per transaction. -/
theorem predecessor_index (D : LiteralByteProtocol.Decoder) (P : OraclePortStoredExperimentC4.Prover)
    (H : Bytes → State) (address : Bytes)
    (read : Read (eval H (Frozen2StartChargePrefix.charged D P)).1 address) :
    firstIdx address (eval H (OraclePortFrozen2Consumer.projected D P)).1 =
    firstIdx address (eval H (Frozen2StartChargePrefix.charged D P)).1 :=
  Frozen2StartChargePrefix.first_start_before_terminal D P H address read

#print axioms original_index
#print axioms predecessor_index
end AspisR1.ART_StartPrefix
end
