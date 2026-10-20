import GeometryInputsLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1GeometryInputs.Proof
open alloc.vec
private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem inputTrace_length (qv : QueryValues) (queries : Array U32 22#usize)
    (start end1 : Nat) (records : List InputRecord)
    (ht : InputTrace qv queries start end1 records) : records.length = end1-start := by
  induction ht with
  | nil n => simp
  | cons i end1 values z tail hi hq ht ih => simp only [List.length_cons]; omega

theorem flatMap_values_length (records : List InputRecord) :
    (records.flatMap (fun e => e.1.val)).length = records.length*5 := by
  induction records with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons,List.length_append,ih,r.1.property,List.length_cons]
    change 5+rs.length*5=(rs.length+1)*5
    omega

theorem geometry_inputs_success_trace (qv : QueryValues) (queries : Array U32 22#usize)
    (start end1 : Usize) (flat zs : Vec M31)
    (h : geometry_inputs_indexed qv queries start end1 = .ok (.Ok (flat,zs))) :
    start.val ≤ end1.val ∧ end1.val ≤ 22 ∧
      ∃ records : List InputRecord, InputTrace qv queries start.val end1.val records ∧
        flat.val = records.flatMap (fun e => e.1.val) ∧
        zs.val = records.map Prod.snd ∧ records.length = end1.val-start.val ∧
        flat.val.length = (end1.val-start.val)*5 ∧ zs.val.length = end1.val-start.val := by
  unfold geometry_inputs_indexed at h
  by_cases hse : start > end1
  · simp only [hse,ite_true] at h
    cases h
  · simp only [hse,ite_false] at h
    rcases bind_ok_inv h with ⟨s,hs,h⟩
    have hsval : s = Array.to_slice queries := (Result.ok.inj hs).symm
    subst s
    have hlen : (Slice.len (Array.to_slice queries)).val = 22 := by
      change queries.val.length=22
      exact queries.property
    by_cases hel : end1 > Slice.len (Array.to_slice queries)
    · simp only [hel,ite_true] at h
      cases h
    · simp only [hel,ite_false] at h
      rcases bind_ok_inv h with ⟨count,_,h⟩
      rcases bind_ok_inv h with ⟨count5,_,h⟩
      rcases bind_ok_inv h with ⟨out,hrun,h⟩
      rcases out with ⟨zs1,flat1,pending⟩
      have hstart : start.val ≤ end1.val := Nat.le_of_not_lt hse
      have hend : end1.val ≤ 22 := by
        have hn : end1.val ≤ (Slice.len (Array.to_slice queries)).val := Nat.le_of_not_lt hel
        simpa only [hlen] using hn
      cases pending with
      | some r =>
        have heq := Result.ok.inj h
        subst r
        exact (loop_no_some_ok qv queries end1 start _ _ zs1 flat1 flat zs hstart hend hrun).elim
      | none =>
        have heq := core.result.Result.Ok.inj (Result.ok.inj h)
        cases heq
        obtain ⟨records,ht,hf,hz⟩ := loop_success_trace qv queries end1 start
          (Vec.with_capacity M31 count) (Vec.with_capacity M31 count5) zs flat hstart hend hrun
        have hv : (Vec.with_capacity M31 count5).val=[] := rfl
        have hzv : (Vec.with_capacity M31 count).val=[] := rfl
        simp only [hv,hzv,List.nil_append] at hf hz
        have hrec := inputTrace_length qv queries start.val end1.val records ht
        refine ⟨hstart,hend,records,ht,hf,hz,hrec,?_,?_⟩
        · rw [hf,flatMap_values_length,hrec]
        · rw [hz,List.length_map,hrec]

#print axioms inputTrace_length
#print axioms flatMap_values_length
#print axioms geometry_inputs_success_trace
end AspisR1GeometryInputs.Proof
