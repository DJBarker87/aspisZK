import NFI_SingleTrace
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFM_Control
open Aeneas Aeneas.Std Result ControlFlow

/-- Each position names an emitted outer iterator state, including termination. -/
def positions : List (Fin 8) := [0,1,2,3,4,5,6,7]
def starts : List Nat := [0,4,8,12,16,20,24]
def pairs : List (Nat × Nat) :=
  [(0,0),(0,1),(0,2),(0,3),(4,4),(4,5),(4,6),(4,7),
   (8,8),(8,9),(8,10),(8,11),(12,12),(12,13),(12,14),(12,15),
   (16,16),(16,17),(16,18),(16,19),(20,20),(20,21),(20,22),(20,23),
   (24,24),(24,25)]
def terms (start : Nat) : List (Nat × Nat) :=
  (List.range (min (start+4) 26-start)).map (fun offset => (start,start+offset))

def skeleton : Nat → NFA_Iterator.Iter → Result (List Usize)
  | 0,_ => ok []
  | fuel+1,iter => do
    let (item,next) ← core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) iter
    match item with
    | none => ok []
    | some start => do
      let rest ← skeleton fuel next
      ok (start::rest)

theorem fixed_terms : starts.flatMap terms=pairs := by rfl

theorem term_count : pairs.length=26 := by rfl

theorem state_sequence : positions.map (fun k => (NFA_Iterator.value k).iter.start.val)=
    [0,4,8,12,16,20,24,26] := by rfl

theorem next_at (k : Fin 7) :
    core.iter.adapters.step_by.IteratorStepBy.next
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (NFA_Iterator.value ⟨k.val,by omega⟩)=
    ok (some (NFA_Iterator.cursor ⟨k.val,by omega⟩),
      NFA_Iterator.value ⟨k.val+1,by omega⟩) := by
  have inside : (NFA_Iterator.value ⟨k.val,by omega⟩).iter.start.val <
      (NFA_Iterator.value ⟨k.val,by omega⟩).iter.end.val := by
    change (NFA_Iterator.cursor ⟨k.val,by omega⟩).val < 26
    rw [NFA_Iterator.start k]; omega
  obtain ⟨next,run,advance,finish,stride⟩ := NFA_Iterator.next
    (NFA_Iterator.value ⟨k.val,by omega⟩) (by rfl) inside
  have hs : next.iter.start=NFA_Iterator.cursor ⟨k.val+1,by omega⟩ := by
    apply UScalar.eq_of_val_eq
    rw [advance]
    fin_cases k <;> rfl
  have ht : next.step_by=4#usize := UScalar.eq_of_val_eq stride
  have same : next=NFA_Iterator.value ⟨k.val+1,by omega⟩ := by
    cases next with
    | mk range step =>
      cases range
      simp_all [NFA_Iterator.value]
  rw [same] at run
  exact run

theorem fixed_outer : skeleton 8 (NFA_Iterator.value 0)=
    ok [0#usize,4#usize,8#usize,12#usize,16#usize,20#usize,24#usize] := by
  rw [skeleton, next_at (0 : Fin 7)]
  simp only [bind_tc_ok, Aeneas.Std.uncurry]
  rw [skeleton, next_at (1 : Fin 7)]
  simp only [bind_tc_ok, Aeneas.Std.uncurry]
  rw [skeleton, next_at (2 : Fin 7)]
  simp only [bind_tc_ok, Aeneas.Std.uncurry]
  rw [skeleton, next_at (3 : Fin 7)]
  simp only [bind_tc_ok, Aeneas.Std.uncurry]
  rw [skeleton, next_at (4 : Fin 7)]
  simp only [bind_tc_ok, Aeneas.Std.uncurry]
  rw [skeleton, next_at (5 : Fin 7)]
  simp only [bind_tc_ok, Aeneas.Std.uncurry]
  rw [skeleton, next_at (6 : Fin 7)]
  simp only [bind_tc_ok, Aeneas.Std.uncurry]
  rw [skeleton,NFA_Iterator.done]
  rfl

/-- Exact emitted-body cut equation. Only input, limbs, fresh sums and the
fixed position occur; no private native iterator representation is postulated. -/
theorem body_at (oracle : NFF_LoggedEight.Oracle)
    (input : NFI_InnerCut.Input) (limbs : Array U64 8#usize) (k : Fin 7) :
    NFF_LoggedOuterStep.step oracle input.q input.g input.slot
      (NFA_Iterator.value ⟨k.val,by omega⟩) limbs = (do
      let sums ← NFF_LoggedLoop.run oracle input.q input.g input.slot
        ((NFA_Iterator.cursor ⟨k.val+1,by omega⟩).val-
         (NFA_Iterator.cursor ⟨k.val,by omega⟩).val)
        {start:=NFA_Iterator.cursor ⟨k.val,by omega⟩,
         «end»:=NFA_Iterator.cursor ⟨k.val+1,by omega⟩}
        (Array.repeat 8#usize 0#u64)
      let out ← NFE_NFA_FoldEight.eight sums limbs
      ok (cont (NFA_Iterator.value ⟨k.val+1,by omega⟩,out))) := by
  obtain ⟨end4,stop,add,minimum,ordered,stopBound,width,meaning⟩ :=
    NFE_NFA_BatchDomain.endpoint (NFA_Iterator.cursor ⟨k.val,by omega⟩)
      (by rw [NFA_Iterator.start k]; omega)
  have same : stop=NFA_Iterator.cursor ⟨k.val+1,by omega⟩ := by
    apply UScalar.eq_of_val_eq
    rw [meaning]
    fin_cases k <;> rfl
  rw [same] at minimum
  rw [NFF_LoggedOuterStep.step,next_at k]
  simp only [bind_tc_ok,Aeneas.Std.uncurry]
  rw [add]
  simp only [bind_tc_ok]
  rw [minimum]
  rfl

theorem stopped (oracle : NFF_LoggedEight.Oracle)
    (input : NFI_InnerCut.Input) (limbs : Array U64 8#usize) :
    NFF_LoggedOuterStep.step oracle input.q input.g input.slot
      (NFA_Iterator.value 7) limbs=ok (done limbs) := by rfl

#print axioms fixed_outer
#print axioms fixed_terms
#print axioms term_count
#print axioms state_sequence
#print axioms next_at
#print axioms body_at
#print axioms stopped
end AspisR1.NFM_Control
end
