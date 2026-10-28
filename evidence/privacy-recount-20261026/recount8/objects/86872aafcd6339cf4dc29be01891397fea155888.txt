import R1Z.ProverRw19ReferenceLength
import R1Z.ProverRw19AuditData
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw19MathematicalAssembly
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw19AuditData

-- A mathematical serialization model, independent of the actual source result.
-- This is NOT yet the whole-model instance: fields/query/node arguments must
-- be constructed from the mathematical protocol at the deployed caller input.
def error : ProverCommitPublish43.Error → verifier.Error
  | .semantic => .Semantic
  | .parse => .Parse
  | .merkle => .Merkle
  | .transcript => .Transcript

def byte (value : UInt8) : U8 := UScalar.mk value.toBitVec

def proofBytes (fields : ProverCommitFront46.Fields)
    (queries : List ProverCommitPublish43.QueryParts)
    (slots : List ProverCommitPublish43.Slot) : Result ByteStatus :=
  match h : ProverCommitFront46.referenceProof fields queries slots with
  | .error e => .ok (.Err (error e))
  | .ok result => .ok (.Ok ⟨result.map byte, by
      rw [List.length_map, ProverRw19AssemblyLength.reference fields queries slots result h]
      scalar_tac⟩)

def output (fields : ProverCommitFront46.Fields)
    (queries : List ProverCommitPublish43.QueryParts)
    (slots : List ProverCommitPublish43.Slot) : Result ProverRw19AuditValue.Status :=
  attachAudit (proofBytes fields queries slots)

theorem bytes (fields : ProverCommitFront46.Fields)
    (queries : List ProverCommitPublish43.QueryParts)
    (slots : List ProverCommitPublish43.Slot) :
    PV_RW_DataProduct.observe PV_RW_DataProduct.first (output fields queries slots) =
      proofBytes fields queries slots := ProverRw19AuditData.bytes _

-- No byte equation against the source, no caller-input-to-fields association,
-- and no release-fixture whole-model equality is assumed or claimed here.
#print axioms error
#print axioms byte
#print axioms proofBytes
#print axioms output
#print axioms bytes
end R1Z.ProverRw19MathematicalAssembly
