import R1Z.ProverCommitCompactSource46
/-! Semantic codec row owner. Metadata recursion is over 27 small source
shapes, not over concrete proof bytes. Native row-context attribution is the
separate per-row Kani certificate; byte slicing/append remain pure std. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitCompactRows46
open Aeneas.Std Result
open ProverCommitPublish43 (Bytes Error)
open ProverCommitCompact43 ProverCommitCompactSource46
attribute [local instance] Classical.propDecidable
structure Shape where
  compact : Bool
  size : Nat

def total (ss : List Shape) := (ss.map (fun s => 5+s.size)).sum

def parsed (s : Shape) (xs : Bytes) : Row :=
  ⟨xs.take 5,s.compact,(xs.drop 5).take s.size,chunks ((xs.drop 5).take s.size)⟩

def parseRows : List Shape → Bytes → List Row
  | [],_ => []
  | s::ss,xs => parsed s xs :: parseRows ss (xs.drop (5+s.size))

def sourceRow (api : API) (s : Shape) (xs out : Bytes) : Except ProverCommitPublish43.Error Bytes :=
  if s.compact then sourceValues api ((xs.drop 5).take s.size) (out ++ xs.take 5)
    else .ok (out ++ xs.take 5 ++ (xs.drop 5).take s.size)

theorem row_source (api : API) (std : TrustedChunks api) (s : Shape)
    (xs out : Bytes) (room : 5+s.size≤xs.length) (multiple : s.size%32=0) :
    sourceRow api s xs out = row (parsed s xs) out := by
  have len : ((xs.drop 5).take s.size).length=s.size := by
    simp only [List.length_take,List.length_drop];omega
  cases h : s.compact with
  | false => simp only [sourceRow,row,parsed,h,Bool.false_eq_true,if_false]
  | true =>
    simp only [sourceRow,row,parsed,h,if_true]
    rw [values_source api std]
    simp only [referenceValues,len,multiple,ne_eq,not_true_eq_false,if_false]

def sourceRows (api : API) : List Shape → Bytes → Bytes → Result (Except ProverCommitPublish43.Error Bytes)
  | [],xs,out => if xs=[] then ok (.ok out) else ok (.error .semantic)
  | s::ss,xs,out =>
    if 5+s.size≤xs.length then
      match sourceRow api s xs out with
      | .error e => ok (.error e)
      | .ok after => sourceRows api ss (xs.drop (5+s.size)) after
    else .fail .panic

theorem rows_source (api : API) (std : TrustedChunks api)
    (ss : List Shape) (xs out : Bytes) (length : xs.length=total ss)
    (multiple : ∀ s∈ss,s.size%32=0) :
    sourceRows api ss xs out = ok (semantic (parseRows ss xs) out) := by
  induction ss generalizing xs out with
  | nil =>
    have empty : xs=[] := List.length_eq_zero_iff.mp length
    subst xs
    simp only [sourceRows,if_true,parseRows,semantic]
  | cons s ss ih =>
    have hlen : xs.length=5+s.size+total ss := by
      simpa only [total,List.map_cons,List.sum_cons] using length
    have room : 5+s.size≤xs.length := by omega
    have rest : (xs.drop (5+s.size)).length=total ss := by
      simp only [List.length_drop];omega
    rw [sourceRows,if_pos room,row_source api std s xs out room (multiple s (List.mem_cons_self ..))]
    rw [parseRows,semantic]
    cases hr : row (parsed s xs) out with
    | error e => simp only [hr,Except.bind]
    | ok next =>
      simp only [hr,Except.bind]
      exact ih _ next rest (fun t ht => multiple t (List.mem_cons_of_mem s ht))

def size (r : Nat) : Nat :=
  if r=2 ∨ r=14 then 32 else if 15≤r ∧ r≤24 then 896
    else if r=25 then 3712 else if r=26 then 928 else 0

def shape (r : Nat) : Shape := ⟨decide (14≤r),size r⟩
def shapes := (List.range 27).map shape

theorem shapes_total : total shapes=13799 := by
  norm_num [total,shapes,shape,size,List.range_succ]

theorem shapes_multiple : ∀ s∈shapes,s.size%32=0 := by
  intro s hs
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hs
  simp only [shape,size]
  split_ifs <;> decide

def sourceCompact (api : API) (logical out : Bytes) : Result (Except ProverCommitPublish43.Error Bytes) :=
  if logical.length≠13831 then ok (.error .semantic)
    else sourceRows api shapes (logical.drop 32) (out ++ logical.take 32)

def referenceCompact (logical out : Bytes) : Except ProverCommitPublish43.Error Bytes :=
  if logical.length≠13831 then .error .semantic
    else semantic (parseRows shapes (logical.drop 32)) (out ++ logical.take 32)

/-- Length rejection occurs before any published output. Every row range and
the final cursor check follow from the fixed source metadata on the other
branch; arbitrary framing and high-half errors remain in the inner result. -/
theorem compact_source (api : API) (std : TrustedChunks api) (logical out : Bytes) :
    sourceCompact api logical out = ok (referenceCompact logical out) := by
  unfold sourceCompact referenceCompact
  by_cases length : logical.length=13831
  · simp only [length,ne_eq,not_true_eq_false,if_false]
    exact rows_source api std shapes _ _
      (by rw [List.length_drop,length,shapes_total]) shapes_multiple
  · simp only [length,ne_eq,not_false_eq_true,if_true]

#print axioms row_source
#print axioms rows_source
#print axioms shapes_total
#print axioms shapes_multiple
#print axioms compact_source
end R1Z.ProverCommitCompactRows46
