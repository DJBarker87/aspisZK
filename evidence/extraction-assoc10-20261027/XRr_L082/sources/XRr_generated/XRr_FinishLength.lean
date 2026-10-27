import XRr_FinishStep
import XRl_LoopInvariant
open Aeneas Aeneas.Std Result XRk_ResultTools XRn_Join_Release
set_option autoImplicit false
namespace XRr_FinishLength
open XRr_FinishStep
theorem loop (b : verifier.BatchedWeights) (it : It) (back out : Back)
 (inv : Inv (it,back))
 (run : verifier.BatchedWeights.finish_loop it back b=ok out) :
 ∀ target, (out target).iter.slice.length=target.iter.slice.length := by
 unfold verifier.BatchedWeights.finish_loop at run
 apply XRl_LoopInvariant.preserve _ Inv
   (fun f => ∀ target, (f target).iter.slice.length=target.iter.slice.length)
   measure ?_ (it,back) out inv run
 intro state r hi hr
 rcases state with ⟨iter,restore⟩
 cases r <;> exact XRr_FinishStep.source b (iter,restore) _ hi hr
/-- All-input partial correctness, including arbitrary pending rows. Failure
is not assumed impossible, and no concrete 64-cell normalization is used. -/
theorem source (b : verifier.BatchedWeights) (weights out : Slice aspis_core.field.QM31)
 (run : verifier.BatchedWeights.finish b weights=ok out) : out.length=weights.length := by
 unfold verifier.BatchedWeights.finish at run
 obtain ⟨im,iterBack,him,run⟩ := pair_bind_success _ _ _ run
 unfold core.slice.Slice.iter_mut at him
 cases Result.ok.inj him
 obtain ⟨it,enumBack,henum,run⟩ := pair_bind_success _ _ _ run
 have henum' : ok ((⟨⟨weights,0⟩,0#usize⟩ : It),
   fun restore : Back => (restore ⟨⟨weights,0⟩,0#usize⟩).iter)=ok (it,enumBack) := henum
 cases Result.ok.inj henum'
 obtain ⟨back,hback,run⟩ := bind_success _ _ _ run
 have frame := loop b ⟨⟨weights,0⟩,0#usize⟩ id back (by intro target;rfl) hback
 have same := Result.ok.inj run
 subst out
 exact frame ⟨⟨weights,0⟩,0#usize⟩
#print axioms loop
#print axioms source
end XRr_FinishLength
