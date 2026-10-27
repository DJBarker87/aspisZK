import XRn_Join_Funs
import AspisR1Post25SamplerIndexedAddSmallCandidate.Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRs_AddStep
abbrev Iter := core.slice.iter.IterMut U32
abbrev Back := Iter → Iter
/-- Common arithmetic, preserving fail and divergence. -/
def step (digit addend : U32) : Result (U32 × U32) := do
 let a ← lift (core.convert.num.FromU64U32.from digit)
 let b ← lift (core.convert.num.FromU64U32.from addend)
 let sum ← a+b
 let p ← lift (core.convert.num.FromU64U32.from 2147483647#u32)
 let rem ← sum % p
 let d ← lift (UScalar.cast .U32 rem)
 let q ← sum / p
 let c ← lift (UScalar.cast .U32 q)
 ok (d,c)

def write (r : Iter) (i : Nat) (d : U32) : Iter :=
 {r with slice := r.slice.setAtNat i d}

theorem emitted (it : Iter) (back : Back) (c : U32)
 (h : it.i < it.slice.val.length) :
 XRn_Join_Release.sampler.add_small_base_p_loop.body it back c =
 (do let (d,c') ← step it.slice.val[it.i] c
     ok (.cont ({it with i := it.i+1},fun r => back (write r it.i d),c'))) := by
 unfold XRn_Join_Release.sampler.add_small_base_p_loop.body
 unfold core.slice.iter.IteratorIterMut.next
 change it.i < it.slice.len.val at h
 rw [dif_pos h]
 simp only [bind_tc_ok, lift, aspis_core.field.P]
 unfold step
 simp only [lift, bind_tc_ok, bind_assoc_eq]
 rfl

theorem exhausted (it : Iter) (back : Back) (c : U32)
 (h : ¬it.i < it.slice.val.length) :
 XRn_Join_Release.sampler.add_small_base_p_loop.body it back c =
 ok (.done (c,back)) := by
 unfold XRn_Join_Release.sampler.add_small_base_p_loop.body
 unfold core.slice.iter.IteratorIterMut.next
 change ¬it.i < it.slice.len.val at h
 rw [dif_neg h]
 rfl

#print axioms emitted
#print axioms exhausted
end XRs_AddStep
