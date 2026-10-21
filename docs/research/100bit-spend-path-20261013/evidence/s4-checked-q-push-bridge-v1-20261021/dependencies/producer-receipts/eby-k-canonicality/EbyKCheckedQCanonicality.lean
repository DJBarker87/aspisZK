import EbyKCheckedQConcreteAll
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1EbyKCheckedQConcreteAll
open AspisR1EbyKCheckedQAllParamV1

private theorem bind_success {α β : Type} (r : Result α) (f : α → Result β) (y : β)
    (h : Bind.bind r f = .ok y) : ∃ x, r=.ok x ∧ f x=.ok y := by
  cases r with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h;cases h
  | div => simp only [bind_tc_div] at h;cases h

theorem fromLimbs_model_eq (x : Q) :
    fromLimbsWithAll concreteAll x =
      (do
        let (b,_) ← allRun fromLimbsClosureFnMut x.val ()
        if b then .ok (some x) else .ok none) := by
  simp only [fromLimbsWithAll,concreteAll,core.slice.Slice.iter,lift,bind_tc_ok,bind_assoc_eq]
  rfl

theorem fromLimbs_success_canonical (x q : Q)
    (hrun : fromLimbsWithAll concreteAll x = .ok (some q)) :
    q=x ∧ ∀ v ∈ q.val, v.val<2147483647 := by
  have hq := fromLimbsWithAll_success_identity concreteAll x q hrun
  subst q
  rw [fromLimbs_model_eq] at hrun
  obtain ⟨pair,hpair,hrest⟩ := bind_success _ _ _ hrun
  rcases pair with ⟨b,n⟩
  cases b with
  | false => cases hrest
  | true => exact ⟨rfl,selected_allRun_true x.val () n hpair⟩

theorem checkedQ_success_canonical (k : Qm) (q : Q)
    (hrun : checkedQWithAll concreteAll k = .ok (.Ok q)) :
    q=Array.make 4#usize [k.c0.a,k.c0.b,k.c1.a,k.c1.b] ∧
      ∀ v ∈ q.val, v.val<2147483647 := by
  have hq := checkedQWithAll_success_limbs concreteAll k q hrun
  have h:=hrun
  unfold checkedQWithAll at h
  obtain ⟨arr,harr,hrest⟩ := bind_success _ _ _ h
  obtain ⟨opt,hopt,hfinal⟩ := bind_success _ _ _ hrest
  cases opt with
  | none => simp only [optionOkOr] at hfinal;cases hfinal
  | some q' =>
    have he : q'=q := core.result.Result.Ok.inj (Result.ok.inj hfinal)
    subst q'
    exact ⟨hq,(fromLimbs_success_canonical arr q hopt).2⟩

#print axioms fromLimbs_model_eq
#print axioms fromLimbs_success_canonical
#print axioms checkedQ_success_canonical
end AspisR1EbyKCheckedQConcreteAll
