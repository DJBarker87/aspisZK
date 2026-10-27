import RPz7_F3U_TwoPass
import RPz7_F3U_Pointwise
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3U_RuntimePointwise
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open AspisV8R19.CausalFirstHitUnionBound
open F3T_Experiment F3T_Charged F3T_TwoPass F3T_ByteCarrier F3T_Carried F3T_Runtime
open RawRecordedOracleExtractionMassBin F3U_CollisionJoin
attribute [local instance] Classical.propDecidable

theorem charge {F C : Type} (c : DrvC_Installation.Configuration F C)
    (D : LiteralByteProtocol.Decoder) (rust : Verifier) (physical : F3T_CanonicalJoin.Physical rust)
    (bad : Exception) (join : Join c D rust bad) (P : ByteProver) (runtime : Runtime)
    (binding : StoredCarrierBinding c D rust P runtime) (H : Bytes → State) :
    runtimeMass (eval H runtime)≤failureMass (eval H (projected D (F3T_Canon.canon (lift c P))))+
      indicator (bad H (eval H P).2.publicBytes (eval H P).2.stored) := by
  unfold runtimeMass
  cases hr : (eval H runtime).2 with
  | none => exact add_nonneg (nonnegative _) (by unfold indicator;split <;> norm_num)
  | some run =>
    apply F3U_Pointwise.failure_charge _ _ _
    intro accepted
    have same := binding H run hr accepted
    have ha : (eval H (annotatedWith D rust (F3T_Canon.canon (lift c P)))).2.2=true := by
      rw [←same];exact accepted
    rcases F3U_TwoPass.annotated_or_collision c D rust physical bad join _ (canon_lift_carried c P) H ha with equal | collision
    · left
      rw [same,equal,projected_eval]
    · right
      simpa only [F3T_Canon.canon_eval,lift_eval,F3T_Canon.canonInput,input] using collision

#print axioms charge
end AspisR1.F3U_RuntimePointwise
end
