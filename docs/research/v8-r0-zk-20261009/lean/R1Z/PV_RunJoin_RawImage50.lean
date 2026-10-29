import R1Z.PV_RunJoin_ScalarRaw50
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RawImage50
open ProverCommitWideOps48

theorem source_injective : Function.Injective source := by
  intro a b h
  exact PV_RunJoin_ScalarRaw50.injective (congrArg ProverRwDictionaryTower.fromW h)

theorem list (n : Nat) (a b : Nat → Raw)
    (h : List.ofFn (fun i : Fin n => source (a i.val))=List.ofFn (fun i : Fin n => source (b i.val))) :
    ∀ i : Fin n,a i.val=b i.val := by
  have hf : (fun i : Fin n => source (a i.val))=(fun i : Fin n => source (b i.val)) := by
    simpa only [List.ofFn_inj] using h
  intro i
  exact source_injective (congrFun hf i)
#print axioms source_injective
#print axioms list
end R1Z.PV_RunJoin_RawImage50
