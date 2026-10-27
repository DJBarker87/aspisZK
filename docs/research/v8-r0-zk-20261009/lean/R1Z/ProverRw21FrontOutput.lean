import R1Z.ProverRw21CompactLengths
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21FrontOutput
open ProverRw21ProtocolOutput ProverRw21CompactRows ProverRw21CompactValues
open ProverRw21ByteLengths ProverRw21CompactLengths
open ProverCommitCompact43 ProverCommitCompactSource46 ProverCommitCompactRows46 ProverCommitFront46
open ProverCommitPublish43 (Bytes)

def compactY1 (t : Transcript) : Bytes := (List.ofFn (fun i => quarter (t.y1 i))).flatten

def front (t : Transcript) : Bytes := header ++ compactSemantic t.semantic ++ compactY1 t ++ suffix (fields t)

theorem y1_length (t : Transcript) : (compactY1 t).length=464 :=
  ofFn_flatten_length _ (fun _ => quarter_length _)

theorem suffix_length (t : Transcript) : (suffix (fields t)).length=2560 := by
  simp only [suffix,fields,List.length_append,wide_length,wides_length,List.length_ofFn]

theorem front_length (t : Transcript) : (front t).length=10055 := by
  simp only [front,List.length_append,compact_semantic_length,y1_length,suffix_length]
  rfl

theorem reference_front (t : Transcript) : referenceFront (fields t)=.ok (front t) := by
  unfold referenceFront
  change (referenceCompact (logical t.semantic) header).bind _ = _
  rw [reference_compact]
  simp only [Except.bind]
  change (referenceValues (wides (fun i => ProverCommitValueRange47.embed (t.y1 i))) _).bind _ = _
  rw [reference_values]
  rfl

#print axioms compactY1
#print axioms front
#print axioms y1_length
#print axioms suffix_length
#print axioms front_length
#print axioms reference_front
end R1Z.ProverRw21FrontOutput
