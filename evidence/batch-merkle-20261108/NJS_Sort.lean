import NJS_SortStep
import Port4B_SortInstall
set_option autoImplicit false
namespace NJS_Sort
open Aeneas Aeneas.Std Result ControlFlow AspisR1 MultiproofSortRef
abbrev Keys := Array U64 16#usize

theorem inner (keys : Keys) (j : Usize) (bound : j.val<16) :
 NJS_Extract.verifier.candidate.sort_batch_keys_loop0_loop0 keys j =
 sort_reference.insert_rows keys j := by
 obtain ⟨observed,model,body,post⟩ := NJS_SortStep.step keys j bound
 cases observed with
 | Done out =>
   unfold NJS_Extract.verifier.candidate.sort_batch_keys_loop0_loop0
   conv_lhs => unfold Aeneas.Std.loop
   conv_rhs => unfold sort_reference.insert_rows
   simp [model,body,NJS_SortStep.control]
 | Next out lower =>
   have descent : lower.val<j.val := by have h:=post.1;omega
   have tail := inner out lower (by omega)
   unfold NJS_Extract.verifier.candidate.sort_batch_keys_loop0_loop0
   conv_lhs => unfold Aeneas.Std.loop
   conv_rhs => unfold sort_reference.insert_rows
   simpa [model,body,NJS_SortStep.control,
     NJS_Extract.verifier.candidate.sort_batch_keys_loop0_loop0] using tail
termination_by j.val

theorem outer_step (iter : core.ops.range.Range Usize) (keys : Keys) (n : Usize)
 (size : n.val≤16) (finish : iter.end=n) (active : iter.start.val<n.val) :
 ∃ iter1,iter1.start.val=iter.start.val+1 ∧ iter1.end=iter.end ∧
 NJS_Extract.verifier.candidate.sort_batch_keys_loop0.body iter keys =
   (do let out←sort_reference.insert_rows keys iter.start;ok (cont (iter1,out))) := by
 obtain ⟨⟨o,iter1⟩,run,ho,hs,he⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_some_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x;rfl) (by intro x y;rfl)
     iter (by rw [finish];exact active))
 subst o
 refine ⟨iter1,hs,he,?_⟩
 simp [NJS_Extract.verifier.candidate.sort_batch_keys_loop0.body,run,inner keys iter.start (by omega)]

theorem outer_stop (iter : core.ops.range.Range Usize) (keys : Keys)
 (terminal : iter.end.val ≤ iter.start.val) :
 NJS_Extract.verifier.candidate.sort_batch_keys_loop0.body iter keys=ok (done keys) := by
 obtain ⟨⟨o,iter1⟩,run,ho,hi⟩ := WP.spec_imp_exists
   (core.iter.range.IteratorRange.next_UScalar_none_spec
     (ty:=.Usize) (cloneInst:=core.clone.CloneUsize)
     (partialOrdInst:=core.cmp.PartialOrdUsize) (by intro x y;rfl) iter terminal)
 subst o
 simp [NJS_Extract.verifier.candidate.sort_batch_keys_loop0.body,run]

theorem outer (fuel : Nat) (iter : core.ops.range.Range Usize) (keys : Keys) (n : Usize)
 (size : n.val≤16) (finish : iter.end=n) (span : iter.start.val+fuel=n.val) :
 NJS_Extract.verifier.candidate.sort_batch_keys_loop0 iter keys=
 sort_reference.sort_rows keys iter.start n := by
 induction fuel generalizing iter keys with
 | zero =>
   have terminal : iter.end.val ≤ iter.start.val := by rw [finish];omega
   have stop := outer_stop iter keys terminal
   have gate : iter.start>=n := by scalar_tac
   unfold NJS_Extract.verifier.candidate.sort_batch_keys_loop0
   conv_lhs => unfold Aeneas.Std.loop
   conv_rhs => unfold sort_reference.sort_rows
   simp [stop,gate]
 | succ fuel ih =>
   obtain ⟨iter1,hs,he,body⟩ := outer_step iter keys n size finish (by omega)
   have increment : (iter.start+1#usize : Result Usize)=ok iter1.start := by
     rw [Port3_Wrapping.checked_add iter.start 1#usize (by change iter.start.val+1≤4096;omega)]
     congr 1
     apply UScalar.eq_of_val_eq
     rw [Port3_Wrapping.increment iter.start (by omega),hs]
   have gate : ¬iter.start>=n := by scalar_tac
   unfold NJS_Extract.verifier.candidate.sort_batch_keys_loop0
   conv_lhs => unfold Aeneas.Std.loop
   conv_rhs => unfold sort_reference.sort_rows
   simp only [body,if_neg gate]
   cases result : sort_reference.insert_rows keys iter.start with
   | fail e => simp [result]
   | div => simp [result]
   | ok out =>
     have tail := ih iter1 out (he.trans finish) (by omega)
     simpa [result,increment,NJS_Extract.verifier.candidate.sort_batch_keys_loop0] using tail

theorem source (keys : Keys) (n : Usize) (positive : 0<n.val) (size : n.val≤16) :
 NJS_Extract.verifier.candidate.sort_batch_keys keys n=sort_reference.sort_rows keys 1#usize n := by
 unfold NJS_Extract.verifier.candidate.sort_batch_keys
 exact outer (n.val-1) {start:=1#usize,«end»:=n} keys n size rfl (by change (1#usize).val+(n.val-1)=n.val;scalar_tac)
#check source
#print axioms inner
#print axioms outer_step
#print axioms outer_stop
#print axioms outer
#print axioms source
end NJS_Sort
