import BatchBackwardLoopInvariant
import M31InverseCanonicalBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchBackward.Proof
open R17CurrentM31Semantics alloc.vec

def currentMul := AspisR1Qm31ArithmeticProbe.field.M31.mul
def currentInv := AspisR1M31Inverse.field.M31.inv currentMul

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem backward_success_inverses (flat pref : Vec U32) (product : U32) (out : Vec U32)
    (hprefsize : flat.val.length ≤ pref.val.length)
    (hprefix : ∀ (j : Nat) (hj : j < flat.val.length) (hp : j < pref.val.length),
      decode (pref.val[j]'hp) = ((flat.val.map decode).take j).prod)
    (hproduct : decode product = (flat.val.map decode).prod)
    (hnonzero : ∀ x ∈ flat.val, decode x ≠ 0)
    (hrun : backward currentMul currentInv flat pref product = .ok out) :
    out.val.length = flat.val.length ∧
      ∀ i, i < flat.val.length → atM out i = (atM flat i)⁻¹ := by
  have hnprod : decode product ≠ 0 := by
    rw [hproduct]
    apply List.prod_ne_zero
    intro hz
    rcases List.mem_map.mp hz with ⟨a,ha,he⟩
    exact hnonzero a ha he
  unfold backward at hrun
  rcases bind_ok_inv hrun with ⟨suffix,hinv,hrun⟩
  rcases bind_ok_inv hrun with ⟨state,hresize,hrun⟩
  rcases bind_ok_inv hrun with ⟨iter,hrev,hloop⟩
  have hiv := AspisR1M31Inverse.SquareProof.current_inv_success_inverse product suffix hnprod hinv
  have hclone : field.M31.Insts.CoreCloneClone.clone field.M31.ZERO = .ok field.M31.ZERO := rfl
  obtain ⟨state1,hr1,hv1⟩ := WP.spec_imp_exists (Vec.resize_spec field.M31.Insts.CoreCloneClone
    (Vec.with_capacity U32 (Vec.len flat)) (Vec.len flat) field.M31.ZERO hclone)
  have heState : state1 = state := Result.ok.inj (hr1.symm.trans hresize)
  subst state1
  have hlen : state.val.length = flat.val.length := by
    rw [hv1,List.length_resize]
    exact Vec.len_val flat
  have heIter : (⟨{start:=0#usize,«end»:=Vec.len flat}⟩ : ReverseRange) = iter := Result.ok.inj hrev
  subst iter
  apply backward_loop_success_inverses currentMul current_mul_decode flat pref hprefsize hprefix
    hnonzero _ suffix state out rfl (by rw [Vec.len_val]) hlen _ _ hloop
  · rw [hiv,hproduct,Vec.len_val,List.take_length]
  · intro i hlo hhi
    have hlenFlat := Vec.len_val flat
    omega

#print axioms backward_success_inverses
end AspisR1BatchBackward.Proof
