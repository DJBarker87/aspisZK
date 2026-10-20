import GeometryInputsStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1GeometryInputs.Proof
open alloc.vec
abbrev InputRecord := Array M31 5#usize × M31
inductive InputTrace (qv : QueryValues) (queries : Array U32 22#usize) : Nat → Nat → List InputRecord → Prop
| nil (n : Nat) : InputTrace qv queries n n []
| cons (i end1 : Nat) (values : Array M31 5#usize) (z : M31) (tail : List InputRecord)
    (hi : i < end1) (hq : qv (queries.val.getD i 0#u32) = .ok (.Ok (values,z)))
    (ht : InputTrace qv queries (i+1) end1 tail) :
    InputTrace qv queries i end1 ((values,z)::tail)

private theorem loop_success_cases {α β : Type} (step : α → Result (ControlFlow α β))
    (state : α) (out : β) (h : Aeneas.Std.loop step state = .ok out) :
    step state = .ok (.done out) ∨
      ∃ stateNext, step state = .ok (.cont stateNext) ∧ Aeneas.Std.loop step stateNext = .ok out := by
  rw [Aeneas.Std.loop.eq_def] at h
  cases hs : step state with
  | fail e => simp [hs] at h
  | div => simp [hs] at h
  | ok cf =>
    cases cf with
    | done result => simp [hs] at h; subst result; exact Or.inl rfl
    | cont stateNext => simp [hs] at h; exact Or.inr ⟨stateNext,rfl,h⟩

theorem loop_no_some_ok (qv : QueryValues) (queries : Array U32 22#usize)
    (end1 i : Usize) (zs flat zs1 flat1 f z : Vec M31)
    (hi : i.val ≤ end1.val) (hend : end1.val ≤ 22)
    (hrun : geometry_inputs_indexed_loop qv queries end1 zs flat i =
      .ok (zs1,flat1,some (.Ok (f,z)))) : False := by
  let step := fun s : Vec M31 × Vec M31 × Usize =>
    geometry_inputs_indexed_loop.body qv queries end1 s.1 s.2.1 s.2.2
  have hloop : Aeneas.Std.loop step (zs,flat,i) = .ok (zs1,flat1,some (.Ok (f,z))) := hrun
  induction hfuel : end1.val-i.val generalizing zs flat i with
  | zero =>
    rcases loop_success_cases step (zs,flat,i) _ hloop with hd | ⟨st,hc,_⟩
    · exact body_no_done_ok qv queries end1 i zs flat zs1 flat1 f z hd
    · rcases st with ⟨z1,f1,j⟩
      obtain ⟨_,_,_,hlt,_,_,_,_⟩ := body_cont qv queries end1 i j zs flat z1 f1 hend hc
      omega
  | succ n ih =>
    rcases loop_success_cases step (zs,flat,i) _ hloop with hd | ⟨st,hc,ht⟩
    · exact body_no_done_ok qv queries end1 i zs flat zs1 flat1 f z hd
    · rcases st with ⟨z1,f1,j⟩
      obtain ⟨_,_,_,hlt,_,_,_,hinc⟩ := body_cont qv queries end1 i j zs flat z1 f1 hend hc
      have hj : j.val ≤ end1.val := by omega
      have hn : end1.val-j.val=n := by omega
      exact ih j z1 f1 hj ht ht hn

theorem loop_success_trace (qv : QueryValues) (queries : Array U32 22#usize)
    (end1 i : Usize) (zs flat zs1 flat1 : Vec M31)
    (hi : i.val ≤ end1.val) (hend : end1.val ≤ 22)
    (hrun : geometry_inputs_indexed_loop qv queries end1 zs flat i = .ok (zs1,flat1,none)) :
    ∃ records : List InputRecord, InputTrace qv queries i.val end1.val records ∧
      flat1.val = flat.val ++ records.flatMap (fun e => e.1.val) ∧
      zs1.val = zs.val ++ records.map Prod.snd := by
  let step := fun s : Vec M31 × Vec M31 × Usize =>
    geometry_inputs_indexed_loop.body qv queries end1 s.1 s.2.1 s.2.2
  have hloop : Aeneas.Std.loop step (zs,flat,i) = .ok (zs1,flat1,none) := hrun
  induction hfuel : end1.val-i.val generalizing zs flat i with
  | zero =>
    rcases loop_success_cases step (zs,flat,i) _ hloop with hd | ⟨st,hc,_⟩
    · obtain ⟨hge,hz,hf⟩ := body_done_none qv queries end1 i zs flat zs1 flat1 hd
      have heq : i.val=end1.val := by omega
      refine ⟨[],?_,?_,?_⟩
      · rw [heq]; exact InputTrace.nil _
      · simp only [hf,List.flatMap_nil,List.append_nil]
      · simp only [hz,List.map_nil,List.append_nil]
    · rcases st with ⟨z1,f1,j⟩
      obtain ⟨_,_,_,hlt,_,_,_,_⟩ := body_cont qv queries end1 i j zs flat z1 f1 hend hc
      omega
  | succ n ih =>
    rcases loop_success_cases step (zs,flat,i) _ hloop with hd | ⟨st,hc,ht⟩
    · obtain ⟨hge,_,_⟩ := body_done_none qv queries end1 i zs flat zs1 flat1 hd
      omega
    · rcases st with ⟨z1,f1,j⟩
      obtain ⟨_,values,z,hlt,hq,hflat,hzs,hinc⟩ := body_cont qv queries end1 i j zs flat z1 f1 hend hc
      have hj : j.val ≤ end1.val := by omega
      have hn : end1.val-j.val=n := by omega
      obtain ⟨records,htrace,hf,hz⟩ := ih j z1 f1 hj ht ht hn
      refine ⟨(values,z)::records,?_,?_,?_⟩
      · apply InputTrace.cons i.val end1.val values z records hlt hq
        simpa only [hinc] using htrace
      · rw [hf,hflat,List.flatMap_cons,List.append_assoc]
      · rw [hz,hzs,List.map_cons,List.append_assoc]
        rfl

#print axioms loop_no_some_ok
#print axioms loop_success_trace
end AspisR1GeometryInputs.Proof
