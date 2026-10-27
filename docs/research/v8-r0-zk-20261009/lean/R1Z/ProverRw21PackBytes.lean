import R1Z.ProverRw21ModelObservations
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21PackBytes
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitPublish43 (Bytes)
abbrev Raw := Except ProverCommitPublish43.Error Bytes

def Bounded (r : Raw) : Prop := ∀ raw, r=.ok raw → raw.length=57607

def pack (r : Raw) (bound : Bounded r) : Result ProverRw19AuditData.ByteStatus :=
  match h : r with
  | .error e => .ok (.Err (ProverRw19MathematicalAssembly.error e))
  | .ok raw => .ok (.Ok ⟨raw.map ProverRw19MathematicalAssembly.byte,by
      rw [List.length_map,bound raw rfl]
      scalar_tac⟩)

theorem congr (r r' : Raw) (bound : Bounded r) (bound' : Bounded r') (h : r=r') :
    pack r bound=pack r' bound' := by cases h; rfl

theorem rejected (r : Raw) (bound : Bounded r) (e : ProverCommitPublish43.Error)
    (h : r=.error e) : pack r bound=.ok (.Err (ProverRw19MathematicalAssembly.error e)) := by
  subst r
  rfl

theorem successful (r : Raw) (bound : Bounded r) (raw : Bytes) (h : r=.ok raw) :
    ∃ proof : alloc.vec.Vec U8, pack r bound=.ok (.Ok proof) ∧
      proof.val=raw.map ProverRw19MathematicalAssembly.byte := by
  subst r
  exact ⟨_,rfl,rfl⟩

theorem assembly (fields : ProverCommitFront46.Fields)
    (queries : List ProverCommitPublish43.QueryParts) (slots : List ProverCommitPublish43.Slot) :
    ProverRw19MathematicalAssembly.proofBytes fields queries slots =
      pack (ProverCommitFront46.referenceProof fields queries slots)
        (fun raw h => ProverRw19AssemblyLength.reference fields queries slots raw h) := by
  unfold ProverRw19MathematicalAssembly.proofBytes
  split
  · rename_i e he
    exact (rejected _ _ e he).symm
  · rename_i raw hr
    obtain ⟨proof,hpack,hval⟩ := successful
      (ProverCommitFront46.referenceProof fields queries slots)
      (fun raw h => ProverRw19AssemblyLength.reference fields queries slots raw h) raw hr
    rw [hpack]
    apply congrArg Result.ok
    apply congrArg core.result.Result.Ok
    apply Subtype.ext
    exact hval.symm

theorem protocol_success (t : ProverRw21ProtocolOutput.Transcript) :
    ProverRw21ModelObservations.proofBytes (.ok (.Ok t)) =
      ProverRw19PreparedAssembly.proofBytes (.ok (.Ok (ProverRw21ProtocolOutput.prepared t))) := rfl

theorem prepared_success (p : ProverRw19PreparedAssembly.Prepared) :
    ProverRw19PreparedAssembly.proofBytes (.ok (.Ok p)) =
      ProverRw19MathematicalAssembly.proofBytes p.1 p.2.1 p.2.2 := by
  rcases p with ⟨fields,queries,slots⟩
  rfl

#print axioms Bounded
#print axioms pack
#print axioms congr
#print axioms rejected
#print axioms successful
#print axioms assembly
#print axioms protocol_success
#print axioms prepared_success
end R1Z.ProverRw21PackBytes
