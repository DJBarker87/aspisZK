import NJS_KeyWord
import NDI_BatchStep
import Port3_Wrapping
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace NJS_KeyStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1

theorem step (queries : Array U32 22#usize) (lo n tree : Usize)
 (iter : core.ops.range.Range Usize) (keys : Array U64 16#usize)
 (size : n.val≤16) (fit : lo.val+n.val≤22) (finish : iter.end=n)
 (active : iter.start.val<n.val) :
 ∃ iter1 value, iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end ∧
 value.val=256*(if tree=2#usize then queries.val[lo.val+iter.start.val]!.val/4
   else queries.val[lo.val+iter.start.val]!.val)+iter.start.val ∧
 NJS_Extract.verifier.candidate.batch_keys_loop.body queries lo tree iter keys=
   ok (cont (iter1,keys.set iter.start value)) := by
 obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_some_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
     iter (by rw [finish];exact active))
 subst o
 obtain ⟨address,add,addressVal⟩ := WP.spec_imp_exists
   (Usize.add_spec (x:=lo) (y:=iter.start) (by scalar_tac))
 have addressEq : Usize.wrapping_add lo iter.start=address := by
   apply UScalar.eq_of_val_eq
   rw [Port3_Wrapping.wrap_add_value lo iter.start (by omega),addressVal]
 obtain ⟨u,read,uval⟩ := WP.spec_imp_exists
   (Array.index_usize_spec queries address (by scalar_tac))
 obtain ⟨divided,division,dividedVal⟩ := UScalar.div_spec (x:=u) (y:=4#u32) (by decide)
 let chosen : U32 := if tree=2#usize then divided else u
 have select : (if tree=2#usize then u / 4#u32 else ok u)=ok chosen := by
   by_cases tag : tree=2#usize <;> simp only [tag,if_true,if_false,chosen,division]
 let value := NJS_KeyWord.pack chosen iter.start
 obtain ⟨changed,write,changedEq⟩ := WP.spec_imp_exists
   (Array.update_spec keys iter.start value (by scalar_tac))
 have room : lo.val+iter.start.val<queries.val.length := by have := queries.property;scalar_tac
 have ue : u=queries.val[lo.val+iter.start.val]! := by
   simpa only [addressVal,List.getElem!_eq_getElem?_getD,
     List.getElem?_eq_getElem room,Option.getD_some] using uval
 refine ⟨iter1,value,hs,he,?_,?_⟩
 · have val := NJS_KeyWord.value chosen iter.start (by omega)
   change value.val=_ at val
   rw [val]
   dsimp [chosen]
   by_cases tag : tree=2#usize
   · simp only [if_pos tag,dividedVal,ue,show (4#u32).val=4 from rfl]
   · simp only [if_neg tag,ue]
 · have body : NJS_Extract.verifier.candidate.batch_keys_loop.body queries lo tree iter keys =
       (do let out←Array.update keys iter.start value;ok (cont (iter1,out))) := by
     simp [NJS_Extract.verifier.candidate.batch_keys_loop.body,run,lift,addressEq,read,select,
       value,NJS_KeyWord.pack]
   rw [body]
   simp only [write,bind_tc_ok,changedEq]

theorem stop (queries : Array U32 22#usize) (lo tree : Usize)
 (iter : core.ops.range.Range Usize) (keys : Array U64 16#usize)
 (done : iter.end.val ≤ iter.start.val) :
 NJS_Extract.verifier.candidate.batch_keys_loop.body queries lo tree iter keys=ok (.done keys) := by
 obtain ⟨⟨o,iter1⟩,run,ho,hi⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_none_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter done)
 subst o
 simp [NJS_Extract.verifier.candidate.batch_keys_loop.body,run]

#print axioms step
#print axioms stop
end NJS_KeyStep
