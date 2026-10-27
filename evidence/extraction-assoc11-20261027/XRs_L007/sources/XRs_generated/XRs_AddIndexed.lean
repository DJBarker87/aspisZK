import XRs_AddStep
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRs_AddIndexed
open XRs_AddStep

theorem write_commute (r : Iter) (i j : Nat) (a b : U32) (h : i ≠ j) :
 write (write r i a) j b = write (write r j b) i a := by
 cases r with | mk s k =>
  unfold write Slice.setAtNat
  congr 2
  exact List.set_comm a b h

def set (a : Array U32 8#usize) (i : Nat) (d : U32) : Array U32 8#usize :=
 ⟨a.val.set i d, by simpa only [List.length_set] using a.property⟩

def idx (i : Nat) (h : i ≤ 8) : Usize := UScalar.ofNat i (by scalar_tac)

theorem body (a : Array U32 8#usize) (c : U32) (i : Nat) (h : i < 8) :
 AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop.body
 a c (idx i (by omega)) =
 (do let (d,c') ← step (a.val[i]'(by simpa only [a.property] using h)) c
     ok (.cont (set a i d,c',idx (i+1) (by omega)))) := by
 unfold AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop.body
 have hi : idx i (by omega) < 8#usize := by change i < 8; exact h
 rw [if_pos hi]
 have ha : i < a.val.length := by have := a.property; change a.val.length = 8 at this; omega
 simp only [Array.index_usize,idx, UScalar.val_ofNat, List.getElem?_eq_getElem ha, bind_tc_ok, lift]
 unfold step
 simp only [lift,bind_tc_ok,bind_assoc_eq]
 unfold AspisR1Post25SamplerIndexedAddSmallCandidate.field.P
 apply congrArg (fun k => (core.convert.num.FromU64U32.from a.val[i] + core.convert.num.FromU64U32.from c) >>= k)
 funext sum
 apply congrArg (fun k => (sum % core.convert.num.FromU64U32.from 2147483647#u32) >>= k)
 funext rem
 simp only [Array.update, List.getElem?_eq_getElem ha,bind_tc_ok]
 apply congrArg (fun k => (sum / core.convert.num.FromU64U32.from 2147483647#u32) >>= k)
 funext q
 have hn : idx i (by omega) + 1#usize = ok (idx (i+1) (by omega)) := by unfold idx; scalar_tac
 rw [hn]
 rfl
#print axioms write_commute
#print axioms body
end XRs_AddIndexed
