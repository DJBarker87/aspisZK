import R1Z.ProverCommitPublish43
/-! Structural compact-value/semantic-row owner. Native cell control is
checked separately; the iterator/chunk representation bridge is not asserted
by naming this owner. Failed partial buffers never become successful bytes. -/
set_option autoImplicit false
namespace R1Z.ProverCommitCompact43
attribute [local instance] Classical.propDecidable
open ProverCommitPublish43 (Bytes Error)
abbrev Cell := Fin 32 → UInt8

def low (cell : Cell) : Bytes := (List.ofFn cell).take 16

def highZero (cell : Cell) : Prop := ∀ i : Fin 16, cell ⟨16+i.val,by omega⟩=0

noncomputable def cell (value : Cell) (out : Bytes) : Except Error Bytes :=
  if highZero value then .ok (out ++ low value) else .error .semantic

theorem low_length (value : Cell) : (low value).length=16 := by
  simp only [low,List.length_take,List.length_ofFn]
  rfl

theorem cell_ok (value : Cell) (out result : Bytes) :
    cell value out = .ok result ↔ highZero value ∧ result=out ++ low value := by
  classical
  unfold cell
  by_cases h : highZero value
  · simp only [h,if_true,Except.ok.injEq,true_and]
    exact eq_comm
  · simp only [h,if_false,false_and]
    constructor <;> intro impossible <;> cases impossible

noncomputable def values : List Cell → Bytes → Except Error Bytes
  | [],out => .ok out
  | c::cs,out => (cell c out).bind (values cs)

noncomputable def valuesLoop (cs : List Cell) (out : Bytes) : Except Error Bytes :=
  cs.foldl (fun result c => result.bind (cell c)) (.ok out)

theorem values_loop (cs : List Cell) (out : Bytes) : valuesLoop cs out=values cs out := by
  have aux : ∀ cs (initial : Except Error Bytes),
      cs.foldl (fun result c => result.bind (cell c)) initial=initial.bind (values cs) := by
    intro cs
    induction cs with
    | nil => intro initial; cases initial <;> rfl
    | cons c cs ih =>
      intro initial
      cases initial with
      | error e => exact ih (.error e)
      | ok out => exact ih (cell c out)
  exact aux cs (.ok out)

theorem values_ok (cs : List Cell) (out result : Bytes) :
    values cs out = .ok result ↔
      (∀ c ∈ cs, highZero c) ∧ result=out ++ (cs.map low).flatten := by
  classical
  induction cs generalizing out with
  | nil => simp only [values,List.not_mem_nil,false_implies,implies_true,List.map_nil,
      List.flatten_nil,List.append_nil,true_and,Except.ok.injEq];exact eq_comm
  | cons c cs ih =>
    unfold values
    by_cases h : highZero c
    · simp only [cell,h,if_true,Except.bind]
      rw [ih]
      simp only [List.mem_cons,forall_eq_or_imp,List.map_cons,List.flatten_cons,
        List.append_assoc,h,true_and]
    · simp only [cell,h,if_false,Except.bind,Except.noConfusion,List.mem_cons,
        forall_eq_or_imp,h,false_and]
      constructor <;> intro impossible <;> cases impossible

theorem values_length (cs : List Cell) (out result : Bytes)
    (ok : values cs out = .ok result) : result.length=out.length+16*cs.length := by
  obtain ⟨_,rfl⟩ := (values_ok cs out result).mp ok
  rw [List.length_append]
  have len : ∀ ds : List Cell, (ds.map low).flatten.length=16*ds.length := by
    intro ds
    induction ds with
    | nil => rfl
    | cons c ds ih =>
      simp only [List.map_cons,List.flatten_cons,List.length_append,low_length,
        ih,List.length_cons]
      omega
  exact congrArg (fun n => out.length+n) (len cs)

structure Row where
  frame : Bytes
  compact : Bool
  raw : Bytes
  cells : List Cell

noncomputable def row (r : Row) (out : Bytes) : Except Error Bytes :=
  if r.compact then values r.cells (out ++ r.frame) else .ok (out ++ r.frame ++ r.raw)

noncomputable def semantic : List Row → Bytes → Except Error Bytes
  | [],out => .ok out
  | r::rs,out => (row r out).bind (semantic rs)

noncomputable def semanticLoop (rs : List Row) (out : Bytes) : Except Error Bytes :=
  rs.foldl (fun result r => result.bind (row r)) (.ok out)

theorem semantic_loop (rs : List Row) (out : Bytes) :
    semanticLoop rs out=semantic rs out := by
  have aux : ∀ rs (initial : Except Error Bytes),
      rs.foldl (fun result r => result.bind (row r)) initial=initial.bind (semantic rs) := by
    intro rs
    induction rs with
    | nil => intro initial; cases initial <;> rfl
    | cons r rs ih =>
      intro initial
      cases initial with
      | error e => exact ih (.error e)
      | ok out => exact ih (row r out)
  exact aux rs (.ok out)

#print axioms low_length
#print axioms cell_ok
#print axioms values_loop
#print axioms values_ok
#print axioms values_length
#print axioms semantic_loop
end R1Z.ProverCommitCompact43
