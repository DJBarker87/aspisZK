import NLW_WriterPair
import NLW_Persistence
set_option autoImplicit false
noncomputable section
namespace NLW_PersistedRoots
open Aeneas Aeneas.Std AspisR1
open AspisR1.CPR_DataPersistence
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical
/-- RuntimePersistence binds only data at the retained live ordinary key.
 The OLD writer's root provenance survives that exact data transport. This
 does not bind a different proof merely because its hash was checked. -/
theorem saved {Tx Key : Type} (next : Tx → Tx → Prop)
 (ordinary : Tx → Key → Prop) (before tentative : Tx → Key → Image)
 (success : Tx → Bool) (loaded : Tx → Key → Option Bytes)
 (law : TwoTransactionLaw next ordinary before tentative success loaded)
 (t u : Tx) (key : Key) (adjacent : next t u) (eligible : ordinary t key)
 (accepted : success t=true) (live : (tentative t key).lamports≠0)
 (oldCheckpoint checkpoint proof pub : Slice U8)
 (write : (tentative t key).data=bytesOf oldCheckpoint.val)
 (read : loaded u key=some (bytesOf checkpoint.val))
 (H : Bytes → State) (p : OraclePortCheckpointAbiC5.Prepared)
 (a : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
 (encoding : bytesOf oldCheckpoint.val=OraclePortCheckpointAbiC5.encode H (bytesOf proof.val) (bytesOf pub.val) p a)
 (roots : NLW_WriterPair.Roots p proof) :
 NLW_CommittedRoots.Both checkpoint proof := by
 have persisted:=NLW_Persistence.loaded_bytes next ordinary before tentative success loaded
  law t u key adjacent eligible accepted live (bytesOf checkpoint.val) read
 rw [write] at persisted
 exact NLW_ByteIdentity.both_transport oldCheckpoint checkpoint proof proof
  (NLW_WriterPair.both H proof pub oldCheckpoint p a encoding roots) persisted rfl
#print saved
#print axioms saved
end NLW_PersistedRoots
