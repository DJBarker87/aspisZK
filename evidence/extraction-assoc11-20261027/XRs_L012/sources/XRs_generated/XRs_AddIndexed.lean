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
 (do let (d,c') ← step (a.val[i]'(by have e := a.property; change a.val.length = 8 at e; omega)) c
     ok (.cont (set a i d,c',idx (i+1) (by omega)))) := by
 unfold AspisR1Post25SamplerIndexedAddSmallCandidate.sampler.add_small_base_p_loop.body
 have hi : idx i (by omega) < 8#usize := by change i < 8; exact h
 rw [if_pos hi]
 have ha : i < a.val.length := by have := a.property; change a.val.length = 8 at this; omega
 have hv : (idx i (by omega)).val = i := rfl
 have hg : a[idx i (by omega)]? = some a.val[i] := by
  change a.val[i]? = _
  exact List.getElem?_eq_getElem ha
 simp only [Array.index_usize,hg, bind_tc_ok, lift]
 unfold step
 simp only [lift,bind_tc_ok,bind_assoc_eq]
 unfold AspisR1Post25SamplerIndexedAddSmallCandidate.field.P
 apply congrArg (fun k => (core.convert.num.FromU64U32.from a.val[i] + core.convert.num.FromU64U32.from c) >>= k)
 funext sum
 apply congrArg (fun k => (sum % core.convert.num.FromU64U32.from 2147483647#u32) >>= k)
 funext rem
 simp only [Array.update, hg,bind_tc_ok]
 apply congrArg (fun k => (sum / core.convert.num.FromU64U32.from 2147483647#u32) >>= k)
 funext q
 have hn : idx i (by omega) + 1#usize = ok (idx (i+1) (by omega)) := by
  obtain ⟨v,hv1,hv2⟩ := WP.spec_imp_exists
   (UScalar.add_spec (x:=idx i (by omega)) (y:=1#usize) (by change i+1 ≤ Usize.max; scalar_tac))
  exact hv1.trans (congrArg ok (UScalar.eq_of_val_eq hv2))
 rw [hn]
 rfl
#print axioms write_commute
#print axioms body
end XRs_AddIndexed
