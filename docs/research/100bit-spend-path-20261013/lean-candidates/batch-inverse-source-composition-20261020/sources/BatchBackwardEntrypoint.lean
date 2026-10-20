import BatchBackwardLoopInvariant
import M31InverseCanonicalBridge
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1BatchBackward.Proof
open R17CurrentM31Semantics alloc.vec

def currentMul := AspisR1Qm31ArithmeticProbe.field.M31.mul
def currentInv := AspisR1M31Inverse.field.M31.inv currentMul

theorem resize_success_length {T : Type} (clone : core.clone.Clone T)
    (base out : alloc.vec.Vec T) (n : Std.Usize) (value : T)
    (h : alloc.vec.Vec.resize clone base n value = .ok out) :
    out.length = n.val := by
  unfold alloc.vec.Vec.resize at h
  split_ifs at h with hlt
  · injection h with hout
    subst out
    simp only [alloc.vec.Vec.length]
    change (List.resize (↑base) n.val value).length = n.val
    simp [List.resize, List.length_append, List.length_take, List.length_replicate,
      Nat.min_eq_left (Nat.le_of_lt hlt), Nat.sub_eq_zero_of_le (Nat.le_of_lt hlt)]
  · have hle : List.length (↑base : List T) ≤ n.val := by
      simpa only [alloc.vec.Vec.length] using (Nat.le_of_not_gt hlt)
    cases hclone : clone.clone value with
    | fail e => simp [hclone] at h
    | div => simp [hclone] at h
    | ok cloned =>
      simp only [hclone, bind_tc_ok] at h
      injection h with hout
      subst out
      simp only [alloc.vec.Vec.length]
      change (List.resize (↑base) n.val cloned).length = n.val
      simp [List.resize, List.length_append, List.length_take, List.length_replicate,
        Nat.min_eq_right hle] <;> omega

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
  have hlen : state.val.length = flat.val.length := by
    have hv := resize_success_length field.M31.Insts.CoreCloneClone
      (Vec.with_capacity U32 (Vec.len flat)) state (Vec.len flat) field.M31.ZERO hresize
    change state.val.length = (Vec.len flat).val at hv
    rw [Vec.len_val] at hv
    exact hv
  have heIter : (⟨{start:=0#usize,«end»:=Vec.len flat}⟩ : ReverseRange) = iter := Result.ok.inj hrev
  subst iter
  apply backward_loop_success_inverses currentMul current_mul_decode flat pref hprefsize hprefix
    hnonzero _ suffix state out rfl (by rw [Vec.len_val]) hlen _ _ hloop
  · rw [hiv,hproduct,Vec.len_val]
    change (flat.val.map decode).prod⁻¹ = ((flat.val.map decode).take flat.val.length).prod⁻¹
    rw [show flat.val.length = (flat.val.map decode).length from by rw [List.length_map],List.take_length]
  · intro i hlo hhi
    change (Vec.len flat).val ≤ i at hlo
    rw [Vec.len_val] at hlo
    exact (Nat.not_lt_of_ge hlo hhi).elim

#print axioms resize_success_length
#print axioms backward_success_inverses
end AspisR1BatchBackward.Proof
