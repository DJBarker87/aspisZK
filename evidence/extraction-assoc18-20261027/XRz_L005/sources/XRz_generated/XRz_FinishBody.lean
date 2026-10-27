import XRx_FinishStep
open Aeneas Aeneas.Std Result ControlFlow XRn_Join_Release
set_option autoImplicit false
namespace XRz_FinishBody
open XRx_FinishStep
def put (i : Nat) (q : Q) : Back := fun t => {t with iter := {t.iter with slice := t.iter.slice.setAtNat i q}}
/-- Symbolic active step: the enumerated index and mutable write are retained. -/
theorem active (b : verifier.BatchedWeights) (w : Slice Q) (i : Usize) (back : Back)
 (active : i.val<w.length) (q : Q) (value : verifier.BatchedWeights.value b i=ok q) :
 ∃ next : Usize, next.val=i.val+1 ∧
 verifier.BatchedWeights.finish_loop.body b ⟨⟨w,i.val⟩,i⟩ back=
 ok (.cont (⟨⟨w,i.val+1⟩,next⟩,fun t => back (put i.val q t))) := by
 have cap : i.val+1≤Usize.max := by have hp : w.length≤Usize.max := w.property; omega
 have hs : WP.spec (i+1#usize : Result Usize) (fun n => n.val=i.val+1) := by
  apply UScalar.add_spec
  simpa only [UScalar.max_USize_eq, show (1#usize).val=1 by decide] using cap
 obtain ⟨next,hnext,hval⟩ := WP.spec_imp_exists hs
 refine ⟨next,by simpa using hval,?_⟩
 unfold verifier.BatchedWeights.finish_loop.body XRn_Join_enumerateNext core.slice.iter.IteratorIterMut.next
 simp only [show i.val < ↑w.len from active, _root_.dite_true,bind_tc_ok,Option.isSome,if_true,hnext,
  Option.map,value]
 dsimp only
 simp only [if_true,bind_tc_ok,value]
 rfl

theorem stopped (b : verifier.BatchedWeights) (w : Slice Q) (i : Usize) (back : Back)
 (stop : ¬i.val<w.length) :
 verifier.BatchedWeights.finish_loop.body b ⟨⟨w,i.val⟩,i⟩ back=ok (.done back) := by
 unfold verifier.BatchedWeights.finish_loop.body XRn_Join_enumerateNext core.slice.iter.IteratorIterMut.next
 simp only [show ¬i.val < ↑w.len from stop,_root_.dite_false,bind_tc_ok,Option.isSome,if_false,Option.map]
 rfl
#print axioms active
#print axioms stopped
end XRz_FinishBody
