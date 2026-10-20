import BatchPrefixExplicitMul
import R17CurrentM31Semantics
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1BatchPrefix.Proof
open R17CurrentM31Semantics
open alloc.vec
abbrev Mul := U32 → U32 → Result U32

def RefinesMul (mul : Mul) : Prop := ∀ a b z, mul a b = .ok z →
  decode z = decode a * decode b

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

private theorem push_success (v out : Vec U32) (x : U32)
    (h : Vec.push v x = .ok out) : out.val = v.val ++ [x] := by
  unfold Vec.push at h
  dsimp only at h
  split at h
  · have he := Result.ok.inj h
    subst out
    exact List.concat_eq_append
  · cases h

private theorem index_success (v : Vec U32) (i : Usize) (x : U32)
    (hi : i.val < v.val.length)
    (h : Vec.index (core.slice.index.SliceIndexUsizeSlice U32) v i = .ok x) :
    x = v.val[i.val] := by
  rw [Vec.index_slice_index] at h
  obtain ⟨out,ho,hv⟩ := WP.spec_imp_exists (Vec.index_usize_spec v i hi)
  have he : out = x := Result.ok.inj (ho.symm.trans h)
  simpa only [he] using hv

theorem body_done (mul : Mul) (flat pref : Vec U32) (product : U32)
    (i : Usize) (out : Vec U32 × U32)
    (h : prefix_product_loop.body mul flat pref product i = .ok (.done out)) :
    flat.val.length ≤ i.val ∧ out = (pref,product) := by
  unfold prefix_product_loop.body at h
  by_cases hi : i < Vec.len flat
  · simp only [hi,ite_true] at h
    rcases bind_ok_inv h with ⟨_,_,h⟩
    rcases bind_ok_inv h with ⟨_,_,h⟩
    rcases bind_ok_inv h with ⟨_,_,h⟩
    rcases bind_ok_inv h with ⟨_,_,h⟩
    cases h
  · simp only [hi,ite_false] at h
    have he := ControlFlow.done.inj (Result.ok.inj h)
    exact ⟨by have hv : ¬i.val < (Vec.len flat).val := hi
              rw [Vec.len_val] at hv
              exact Nat.le_of_not_lt hv,he.symm⟩

theorem body_cont (mul : Mul) (hr : RefinesMul mul)
    (flat pref pref1 : Vec U32) (product product1 : U32) (i i1 : Usize)
    (h : prefix_product_loop.body mul flat pref product i = .ok (.cont (pref1,product1,i1))) :
    ∃ hi : i.val < flat.val.length,
      pref1.val = pref.val ++ [product] ∧
      decode product1 = decode product * decode flat.val[i.val] ∧
      i1.val = i.val + 1 := by
  unfold prefix_product_loop.body at h
  by_cases hi : i < Vec.len flat
  · simp only [hi,ite_true] at h
    rcases bind_ok_inv h with ⟨p1,hpush,h⟩
    rcases bind_ok_inv h with ⟨x,hread,h⟩
    rcases bind_ok_inv h with ⟨prod1,hmul,h⟩
    rcases bind_ok_inv h with ⟨j,hinc,h⟩
    have he := ControlFlow.cont.inj (Result.ok.inj h)
    cases he
    have hiN : i.val < flat.val.length := by
      have hv : i.val < (Vec.len flat).val := hi
      rw [Vec.len_val] at hv
      exact hv
    refine ⟨hiN,push_success pref pref1 product hpush,?_,?_⟩
    · rw [hr product x product1 hmul,index_success flat i x hiN hread]
    · have hs := UScalar.add_equiv i 1#usize
      rw [hinc] at hs
      simpa only [show (1#usize).val = 1 from rfl] using hs.2.1
  · simp only [hi,ite_false] at h
    cases h

#print axioms body_done
#print axioms body_cont
end AspisR1BatchPrefix.Proof
