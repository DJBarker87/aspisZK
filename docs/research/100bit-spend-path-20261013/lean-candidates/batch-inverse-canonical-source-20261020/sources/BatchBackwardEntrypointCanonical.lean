import BatchBackwardLoopCanonical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchBackward.Proof
open R17CurrentM31Semantics alloc.vec

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem backward_success_canonical (inv : U32 → Result U32)
    (flat pref : Vec U32) (product : U32) (out : Vec U32)
    (hrun : backward currentMul inv flat pref product = .ok out) : CanonicalVec out := by
  unfold backward at hrun
  rcases bind_ok_inv hrun with ⟨suffix,_,hrun⟩
  rcases bind_ok_inv hrun with ⟨state,hresize,hrun⟩
  rcases bind_ok_inv hrun with ⟨iter,hrev,hloop⟩
  have hclone : field.M31.Insts.CoreCloneClone.clone field.M31.ZERO = .ok field.M31.ZERO := rfl
  obtain ⟨state1,hr1,hv1⟩ := WP.spec_imp_exists (Vec.resize_spec field.M31.Insts.CoreCloneClone
    (Vec.with_capacity U32 (Vec.len flat)) (Vec.len flat) field.M31.ZERO hclone)
  have heState : state1 = state := Result.ok.inj (hr1.symm.trans hresize)
  subst state1
  have hvals : state.val = List.replicate (Vec.len flat).val field.M31.ZERO := by
    rw [hv1]
    simp [List.resize,Vec.with_capacity,Vec.new]
  have hcanon : CanonicalVec state := by
    intro x hx
    rw [hvals] at hx
    rcases List.mem_replicate.mp hx with ⟨_,he⟩
    subst x
    rw [field.M31.ZERO]
    change (0:Nat) < 2147483647
    decide
  have hlen : state.val.length = (Vec.len flat).val := by rw [hvals,List.length_replicate]
  have heIter : (⟨{start:=0#usize,«end»:=Vec.len flat}⟩ : ReverseRange) = iter := Result.ok.inj hrev
  subst iter
  exact backward_loop_success_canonical flat pref _ suffix state out rfl
    (by change (Vec.len flat).val ≤ state.val.length; rw [hlen]) hcanon hloop

#print axioms backward_success_canonical
end AspisR1BatchBackward.Proof
