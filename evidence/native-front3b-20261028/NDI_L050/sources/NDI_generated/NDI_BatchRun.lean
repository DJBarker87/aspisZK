import NDI_BatchStep
import NBI_Keys
set_option autoImplicit false
namespace NDI_BatchRun
open Aeneas Aeneas.Std Result ControlFlow AspisR1

theorem frame_all (keys : Array U64 16#usize) (j : Usize) (value : U64)
    (active : j.val<16) (k : Nat) :
    (keys.set j value).val[k]! =(if k=j.val then value else keys.val[k]!) := by
  by_cases hit : j.val=k
  · subst k
    exact NDI_BatchStep.frame keys j value j.val active
  · simp only [Array.set,List.getElem!_eq_getElem?_getD,List.getElem?_set_ne hit,
      if_neg (Ne.symm hit)]

theorem run (queries : Array U32 22#usize) (lo n tree j : Usize) (keys : Array U64 16#usize)
    (word : Nat → U64) (size : n.val≤16) (fit : lo.val+n.val≤22) (bound : j.val≤n.val)
    (spec : ∀ k, k<n.val → (word k).val=
      256*(if tree=2#usize then queries.val[lo.val+k]!.val/4
        else queries.val[lo.val+k]!.val)+k) :
    ∃ final, NDI_BatchRef.batch_keys_ref_loop queries lo n tree keys j=ok final ∧
      ∀ k, final.val[k]! =NBE_KeyLoop.fill word (n.val-j.val) j.val (fun c=>keys.val[c]!) k := by
  by_cases active : j.val<n.val
  · obtain ⟨next,value,nextVal,valueVal,body⟩ := NDI_BatchStep.step queries lo n tree j keys size fit active
    have eq : value=word j.val := UScalar.eq_of_val_eq (valueVal.trans (spec j.val active).symm)
    subst value
    obtain ⟨final,tail,cells⟩ := run queries lo n tree next (keys.set j (word j.val)) word size fit (by omega) spec
    refine ⟨final,?_,?_⟩
    · unfold NDI_BatchRef.batch_keys_ref_loop
      conv_lhs => unfold loop
      simpa only [body,NDI_BatchRef.batch_keys_ref_loop] using tail
    · intro k
      rw [cells k,show n.val-j.val=(n.val-next.val)+1 by omega,NBE_KeyLoop.fill]
      simp only [nextVal]
      congr 1
      funext c
      exact frame_all keys j (word j.val) (by omega) c
  · have last : j.val=n.val := by omega
    refine ⟨keys,?_,?_⟩
    · unfold NDI_BatchRef.batch_keys_ref_loop
      conv_lhs => unfold loop
      simp only [NDI_BatchStep.done_step queries lo n tree j keys (by omega)]
    · intro k
      simp only [last,Nat.sub_self,NBE_KeyLoop.fill]
termination_by n.val-j.val

#print axioms frame_all
#print axioms run
end NDI_BatchRun
