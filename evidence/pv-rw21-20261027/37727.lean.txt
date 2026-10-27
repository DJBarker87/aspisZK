import R1Z.ProverRw21SemanticRows
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw21CompactRows
open ProverRw21ProtocolOutput ProverRw21ParseRows ProverRw21SemanticRows
open ProverCommitCompact43 ProverCommitCompactSource46 ProverCommitCompactRows46
open ProverCommitPublish43 (Bytes)

def compactWire (r : RowData) : Bytes :=
  r.frame ++ if r.shape.compact then ((chunks r.raw).map low).flatten else r.raw

def Range (r : RowData) : Prop := r.shape.compact=true → ∀ c∈chunks r.raw,highZero c

theorem row_model (r : RowData) (valid : Range r) (out : Bytes) :
    row (ProverRw21ParseRows.model r) out = .ok (out ++ compactWire r) := by
  unfold row ProverRw21ParseRows.model compactWire
  split
  · rename_i hc
    rw [(values_ok _ _ _).mpr ⟨valid hc,rfl⟩]
    rw [List.append_assoc]
  · rw [List.append_assoc]

theorem rows_model (rs : List RowData) (valid : ∀ r∈rs,Range r) (out : Bytes) :
    semantic (rs.map ProverRw21ParseRows.model) out = .ok (out ++ (rs.map compactWire).flatten) := by
  induction rs generalizing out with
  | nil => simp only [List.map_nil,List.flatten_nil,List.append_nil,semantic]
  | cons r rs ih =>
    simp only [List.map_cons,List.flatten_cons,semantic]
    rw [row_model r (valid r (List.mem_cons_self ..)) out]
    simp only [Except.bind]
    rw [ih (fun q hq => valid q (List.mem_cons_of_mem r hq)),List.append_assoc]

theorem range_row (s : Semantic) (r : Fin 27) : Range (rowData s r) := by
  intro hc
  apply compact_payload s r
  change decide (14≤r.val)=true at hc
  exact of_decide_eq_true hc

def compactSemantic (s : Semantic) : Bytes :=
  List.ofFn s.root1 ++ ((List.ofFn (rowData s)).map compactWire).flatten

theorem reference_compact (s : Semantic) (out : Bytes) :
    referenceCompact (logical s) out=.ok (out ++ compactSemantic s) := by
  unfold referenceCompact
  rw [ProverRw21SemanticLengths.logical_length]
  simp only [ne_eq,not_true_eq_false,if_false]
  have drop : (logical s).drop 32=(List.ofFn (record s)).flatten := by
    unfold logical
    simpa only [List.length_ofFn] using (List.drop_left (l₁ := List.ofFn s.root1) (l₂ := (List.ofFn (record s)).flatten))
  have take : (logical s).take 32=List.ofFn s.root1 := by
    unfold logical
    simpa only [List.length_ofFn] using (List.take_left (l₁ := List.ofFn s.root1) (l₂ := (List.ofFn (record s)).flatten))
  rw [drop,take,parsed_records,rows_model _ (by
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    exact range_row s i)]
  rw [List.append_assoc]
  rfl

#print axioms compactWire
#print axioms Range
#print axioms row_model
#print axioms rows_model
#print axioms range_row
#print axioms compactSemantic
#print axioms reference_compact
end R1Z.ProverRw21CompactRows
