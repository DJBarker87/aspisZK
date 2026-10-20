import BatchPrefixStepSemantics
import R1ZBatchInverseSourceModelV4
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1BatchPrefix.Proof
open R17CurrentM31Semantics
open alloc.vec R1ZBatchInverseSourceModelV1

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

theorem loop_success_model (mul : Mul) (hr : RefinesMul mul)
    (flat pref : Vec U32) (product : U32) (i : Usize) (out : Vec U32 × U32)
    (hi : i.val ≤ flat.val.length)
    (hrun : prefix_product_loop mul flat pref product i = .ok out) :
    out.1.val.map decode = pref.val.map decode ++
        prefixRun ((flat.val.drop i.val).map decode) (decode product) ∧
    decode out.2 = decode product * ((flat.val.drop i.val).map decode).prod := by
  let step := fun s : Vec U32 × U32 × Usize => prefix_product_loop.body mul flat s.1 s.2.1 s.2.2
  have hloop : Aeneas.Std.loop step (pref,product,i) = .ok out := hrun
  induction hfuel : flat.val.length - i.val generalizing pref product i with
  | zero =>
    have hge : flat.val.length ≤ i.val := by omega
    rcases loop_success_cases step (pref,product,i) out hloop with hd | ⟨st,hc,_⟩
    · have hv := body_done mul flat pref product i out hd
      rw [hv.2]
      simp only [List.drop_eq_nil_of_le hge,List.map_nil,prefixRun,List.append_nil,List.prod_nil,mul_one]
      constructor <;> trivial
    · rcases st with ⟨p1,v1,j⟩
      obtain ⟨hlt,_,_,_⟩ := body_cont mul hr flat pref p1 product v1 i j hc
      omega
  | succ n ih =>
    rcases loop_success_cases step (pref,product,i) out hloop with hd | ⟨st,hc,ht⟩
    · have hv := body_done mul flat pref product i out hd
      omega
    · rcases st with ⟨p1,v1,j⟩
      obtain ⟨hlt,hpref,hprod,hinc⟩ := body_cont mul hr flat pref p1 product v1 i j hc
      have hj : j.val ≤ flat.val.length := by omega
      have hn : flat.val.length - j.val = n := by omega
      have hnext : prefix_product_loop mul flat p1 v1 j = .ok out := ht
      have hs := ih p1 v1 j hj hnext ht hn
      have hdrop := List.drop_eq_getElem_cons hlt
      rw [hinc] at hs
      rw [hpref,List.map_append,List.map_singleton,hprod] at hs
      rw [hdrop,List.map_cons,prefixRun,List.prod_cons]
      constructor
      · rw [hs.1,List.append_assoc]
        rfl
      · rw [hs.2,mul_assoc]

#print axioms loop_success_model
end AspisR1BatchPrefix.Proof
