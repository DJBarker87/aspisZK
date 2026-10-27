import RPz7_FGl_Join
import RPz7_F3Y_Event
set_option autoImplicit false
noncomputable section
namespace AspisR1.FGl_CollisionLaw
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open DrvC_Installation F3T_ByteCarrier

theorem joined {F C : Type} (base : Configuration F C)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (D : LiteralByteProtocol.Decoder) (w : CanonicalCutEnrichedTranscript.Words)
    (prior : Program Bytes State Unit) (Q : Nat)
    (queries : ∀ H : Bytes → State,(eval H prior).1.length≤Q)
    (select : F3X_Projection.Output → R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs) :
    let c := F3V_Install.configuration base
    ∀ (prepareOwner : WAdm_Domain.SessionAPrepare
      (Tx1Q_Execution.actual (Op5T_Concrete.current c.currentBase) c.reserved c.query c.geometry c.boundaries c.std))
    (primitiveOwner : Port5Q1_QueryPorts.SessionAPrimitives c.query)
    (canonicalOwner : Port5Q1_GeometryCanonical.SessionAPrimitives c.geometry)
    (domainOwner : Port5Q1_Domain.SessionADomain c.geometry)
    (multiply : c.geometry.op9=AspisR1Qm31ArithmeticProbe.field.M31.mul)
    (one : c.geometry.op7=ok (1#u32)) (inverse : c.geometry.op11=Port4C_InverseExecution.inverse_owned)
    (finishOwners : FGl_PreparedAt.Owners c base.boundaries),
    F3U_CollisionJoin.Join c D (F3T_Installed.source c hashv)
      (F3Y_Event.bad c hashv prior Q select) := by
  dsimp only
  intro prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse finishOwners
  exact FGl_Join.accepted_raw_join_or_collision base hashv D w prior Q queries select
    prepareOwner primitiveOwner canonicalOwner domainOwner multiply one inverse finishOwners

#print axioms joined
end AspisR1.FGl_CollisionLaw
end
