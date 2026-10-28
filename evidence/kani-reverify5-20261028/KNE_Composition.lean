import KNE_Schedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.KNE_Composition
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open KNE_Model KNE_Schedule KNE_Caller KND_Schedule
open CheckpointBytes5Effect CheckpointBytes5Writer CheckpointBytesBody CheckpointBytesBlocks CheckpointBytesDigest

-- Physical step relation after decoding live bytes. The evidence interprets
-- this relation under the retained allocator/library/source association.
def LocalCorrect (native : Bytes → Bytes → Bytes → Prop) (ss : List Step) : Prop :=
  ∀ s ∈ ss, ∀ before value after,
    before.length = s.len → value.length = s.size → native before value after →
    after = before ++ value

inductive Trace (native : Bytes → Bytes → Bytes → Prop) :
    List (String × Bytes) → Bytes → Bytes → Prop where
  | done (before : Bytes) : Trace native [] before before
  | step (op : String) (value : Bytes) (rest : List (String × Bytes))
      (before middle after : Bytes) (call : native before value middle)
      (tail : Trace native rest middle after) :
      Trace native ((op,value)::rest) before after

theorem compose {native : Bytes → Bytes → Bytes → Prop}
    {es : List (String × Bytes)} {before after : Bytes}
    (tr : Trace native es before after) :
    LocalCorrect native (annotate before.length (shape es)) →
      after = before ++ payload es := by
  induction tr with
  | done before =>
    intro valid
    simp [payload]
  | step op value rest before middle after call tail ih =>
    intro valid
    have head : (⟨op,before.length,1768,value.length⟩ : Step) ∈
        annotate before.length (shape ((op,value)::rest)) := by
      simp [shape,annotate]
    have mid := valid _ head before value middle rfl rfl call
    have tailValid : LocalCorrect native (annotate middle.length (shape rest)) := by
      intro s hs b v out hb hv run
      apply valid s _ b v out hb hv run
      simp only [shape,List.map_cons,annotate,List.mem_cons]
      right
      simpa only [mid,List.length_append,shape] using hs
    rw [ih tailValid,mid]
    simp [payload,List.append_assoc]

theorem annotate_left (n : Nat) (xs ys : List (String × Nat)) (s : Step)
    (member : s ∈ annotate n xs) : s ∈ annotate n (xs ++ ys) := by
  induction xs generalizing n with
  | nil => simp [annotate] at member
  | cons x xs ih =>
    simp only [annotate,List.mem_cons,List.cons_append] at member ⊢
    rcases member with h | h
    · exact Or.inl h
    · exact Or.inr (ih _ h)

theorem body_entries (p : Prepared) (a : Accumulator) (domain : WriterDomain p a)
    (hp hu hc : Digest) (s : Step)
    (member : s ∈ annotate 0 (shape (bodyEmissions
      (fields p a domain.size domain.queriesBound) (stateOf hp) (stateOf hu)))) :
    s ∈ schedule := by
  have h := annotate_left 0 _ [("checksum",32)] s member
  have whole := writer_shape (fields p a domain.size domain.queriesBound)
    (stateOf hp) (stateOf hu) (stateOf hc)
  change shape (bodyEmissions _ _ _) ++ [("checksum",32)] = emissions at whole
  rw [whole] at h
  exact h

-- The missing runtime premises are per-step laws, never a whole-output law.
theorem body_bytes (native : Bytes → Bytes → Bytes → Prop)
    (valid : LocalCorrect native schedule)
    (p : Prepared) (a : Accumulator) (domain : WriterDomain p a)
    (hp hu hc : Digest) (body : Slice U8)
    (tr : Trace native (bodyEmissions (fields p a domain.size domain.queriesBound)
      (stateOf hp) (stateOf hu)) [] (MultiproofConeCanonical.bytesOf body.val)) :
    MultiproofConeCanonical.bytesOf body.val =
      LPm_CheckpointBody.nativeBody p a domain.size domain.queriesBound hp hu := by
  have flat := compose tr (fun s hs => valid s (body_entries p a domain hp hu hc s hs))
  simpa only [List.nil_append,native_body_decomposition p a domain hp hu] using flat

#print axioms compose
#print axioms annotate_left
#print axioms body_entries
#print axioms body_bytes
end AspisR1.KNE_Composition
end
