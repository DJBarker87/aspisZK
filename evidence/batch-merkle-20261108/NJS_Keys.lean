import NJS_KeyStep
import NDI_BatchInstalled
set_option autoImplicit false
namespace NJS_Keys
open Aeneas Aeneas.Std Result ControlFlow AspisR1

theorem loop (queries : Array U32 22#usize) (lo n tree : Usize) (fuel : Nat)
 (iter : core.ops.range.Range Usize) (keys : Array U64 16#usize)
 (size : n.val≤16) (fit : lo.val+n.val≤22) (finish : iter.end=n)
 (span : iter.start.val+fuel=n.val) :
 NJS_Extract.verifier.candidate.batch_keys_loop iter queries lo tree keys =
 NDI_BatchRef.batch_keys_ref_loop queries lo n tree keys iter.start := by
 induction fuel generalizing iter keys with
 | zero =>
   have terminal : n.val ≤ iter.start.val := by omega
   have sourceDone := NJS_KeyStep.stop queries lo tree iter keys (by rw [finish];exact terminal)
   have referenceDone := NDI_BatchStep.done_step queries lo n tree iter.start keys terminal
   unfold NJS_Extract.verifier.candidate.batch_keys_loop NDI_BatchRef.batch_keys_ref_loop
   conv_lhs => unfold Aeneas.Std.loop
   conv_rhs => unfold Aeneas.Std.loop
   simp [sourceDone,referenceDone]
 | succ fuel ih =>
   obtain ⟨iter1,value,hs,he,hv,body⟩ := NJS_KeyStep.step queries lo n tree iter keys size fit finish (by omega)
   obtain ⟨next,oldvalue,nextVal,oldVal,oldBody⟩ := NDI_BatchStep.step queries lo n tree iter.start keys size fit (by omega)
   have sameValue : oldvalue=value := UScalar.eq_of_val_eq (oldVal.trans hv.symm)
   have sameNext : next=iter1.start := UScalar.eq_of_val_eq (by omega)
   have refBody : NDI_BatchRef.batch_keys_ref_loop.body queries lo n tree keys iter.start =
       ok (cont (keys.set iter.start value,iter1.start)) := by
     simpa only [sameValue,sameNext] using oldBody
   have tail := ih iter1 (keys.set iter.start value) (he.trans finish) (by omega)
   unfold NJS_Extract.verifier.candidate.batch_keys_loop NDI_BatchRef.batch_keys_ref_loop
   conv_lhs => unfold Aeneas.Std.loop
   conv_rhs => unfold Aeneas.Std.loop
   simpa [body,refBody,NJS_Extract.verifier.candidate.batch_keys_loop,
     NDI_BatchRef.batch_keys_ref_loop] using tail

theorem source (raw : Array U32 22#usize) (lo n tree : Usize)
 (split : (lo=0#usize ∧ n=10#usize) ∨ (lo=10#usize ∧ n=12#usize))
 (kind : tree.val<3) (canonical : ∀ k,k<22 → raw.val[k]!.val<262144) :
 NJS_Extract.verifier.candidate.batch_keys raw lo n tree = Port4B_KeyInstall.build raw lo n tree := by
 have size : n.val≤16 := by rcases split with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
 have fit : lo.val+n.val≤22 := by rcases split with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> decide
 calc
  NJS_Extract.verifier.candidate.batch_keys raw lo n tree = NDI_BatchRef.batch_keys_ref raw lo n tree := by
   unfold NJS_Extract.verifier.candidate.batch_keys NDI_BatchRef.batch_keys_ref
   exact loop raw lo n tree n.val {start:=0#usize,«end»:=n} _ size fit rfl (by simp)
  _ = Port4B_KeyInstall.build raw lo n tree := NDI_BatchInstalled.installed raw lo n tree split kind canonical

#check source
#print axioms loop
#print axioms source
end NJS_Keys
