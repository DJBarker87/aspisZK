import XRx_ValueOwned
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XRz_FinishValue
abbrev Q := aspis_core.field.QM31
def newQ (q : S8OwnedP6ValueModel.Q) : Q := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
theorem inverse (q : Q) : newQ (XRx_ValueOwned.oldQ q)=q := rfl
theorem source (b : verifier.BatchedWeights) (i : Usize) (bound : i.val<b.raw.length) :
 verifier.BatchedWeights.value b i=ok (newQ (S8OwnedP6Finish.modelValue b.raw.val[i.val])) := by
 obtain ⟨_,_,_,_,w,x,y,z,_,run,_,_,_,_⟩ := XRx_ValueRow.source b i bound
 have eq := XRx_ValueOwned.source b i bound
 rw [run,S8OwnedP6Finish.modelValue_success] at eq
 have h := congrArg newQ (Result.ok.inj eq)
 change (⟨⟨w,x⟩,⟨y,z⟩⟩ : Q) = _ at h
 exact run.trans (congrArg Result.ok h)
#print axioms inverse
#print axioms source
end XRz_FinishValue
