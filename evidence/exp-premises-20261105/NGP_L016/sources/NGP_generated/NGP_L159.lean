import NGK_COMBINED_IMPORT
import NGC_KNE_Writer

/-! Specification only. Supplying Cuts is not evidence that a physical run
realizes them; the realization is an OPEN producer obligation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGP_L159
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MultiproofConeCanonical

/-- Exact same-run values to be exported by TX1:186 and Pool B/D. No law is
stored in this record, and no independently existential successful run is used. -/
structure Cuts where
  proof1 : Slice U8
  public1 : Slice U8
  proof2 : Slice U8
  public2 : Slice U8
  checkpointRead : Slice U8
  saved : alloc.vec.Vec U8
  emittedStatement : NFY_NEU_EmitModel.Statement
  poolRead : NGK_NFO_ReadModel.Accepted

/-- L159's byte/history/Pool conclusion on the current carriers. The full
source-to-cuts realization, native acceptance and game are producer inputs,
not implicit consequences of this definition. No slot/epoch field exists in
CPG_Projection; bank-lineage adjacency is the precise current order. -/
def L159_statement {Tx A : Type} (p : CPG_Projection.Observations Tx A)
    (t u : Tx) (c : Cuts) : Prop :=
  let key := ((p.layout t).handles 2).1
  CPG_Projection.adjacent p t u ∧
  key = ((p.layout u).handles 6).1 ∧
  CPG_Projection.success p t = true ∧
  p.copied t = c.saved ∧
  c.saved.val.length = 1768 ∧
  CPG_Projection.loaded p u key = some (bytesOf c.saved.val) ∧
  bytesOf c.checkpointRead.val = bytesOf c.saved.val ∧
  bytesOf c.proof2.val = bytesOf c.proof1.val ∧
  bytesOf c.public2.val = bytesOf c.public1.val ∧
  c.poolRead.bytes = (S2K.ResultPayload.bytes c.emittedStatement).val ∧
  c.poolRead.value = S2K.ResultAdmission.value c.emittedStatement

/-- The outstanding writer association is this SAME p/a/domain/proof/public,
not a hash-only equality or a second selected prepared state. -/
def Writer_statement (p : CheckpointBytes5Writer.Prepared)
    (a : CheckpointBytes5Writer.Accumulator)
    (domain : NGC_KNE_Caller.WriterDomain p a) (proof public1 : Slice U8) : Prop :=
  NGC_KNE_Writer.sourceProgram p a domain proof public1 =
    CheckpointBytes5Writer.writer p a proof public1

/-- RuntimePersistence does not frame owner, metadata, lamports or SDK borrows.
This sublemma isolates its exact data-only contribution after source protection. -/
theorem persisted_bytes {Tx Key : Type}
    (next : Tx → Tx → Prop) (ordinary : Tx → Key → Prop)
    (before tentative : Tx → Key → CPR_DataPersistence.Image)
    (success : Tx → Bool) (loaded : Tx → Key → Option Bytes)
    (law : CPR_DataPersistence.TwoTransactionLaw next ordinary before tentative success loaded)
    (t u : Tx) (key : Key) (adjacent : next t u) (eligible : ordinary t key)
    (parent : success t = true) (positive : (tentative t key).lamports ≠ 0)
    (saved : Bytes) (written : (tentative t key).data = saved) :
    loaded u key = some saved := by
  rw [law t u adjacent key eligible, parent]
  simp only [if_true, CPR_DataPersistence.visible, positive, if_false, written]

#print axioms persisted_bytes
#print axioms L159_statement
#print axioms Writer_statement
end AspisR1.NGP_L159
