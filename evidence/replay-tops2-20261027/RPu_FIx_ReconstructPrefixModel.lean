import RPu_FIx_ReconstructValue
import RPu_SelectorReconstructIndexModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ReconstructPrefixModel
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K decode)

theorem take_step {A : Type} (xs : List A) (n : Nat) (bound : n<xs.length) :
    xs.take (n+1)=xs.take n++[xs[n]'bound] := by
  induction xs generalizing n with
  | nil => cases bound
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [List.take_succ_cons,List.getElem_cons_succ,List.cons_append]
      rw [ih n (by simp only [List.length_cons] at bound;omega)]

theorem model_append (xs : List NQ) (x : NQ) (acc : K) :
    FIx_ReconstructFold.model (xs++[x]) acc=FIx_ReconstructFold.model xs ((acc+acc)+decode x) := by
  simp only [FIx_ReconstructFold.model,List.reverse_append,List.reverse_singleton,List.singleton_append,
    List.map_cons,List.foldl_cons]

theorem value (view : Array NQ 16#usize) (n : Nat) (bound : n≤view.val.length) (acc : K) :
    FIx_ReconstructFold.model (view.val.take n) acc=
      SelectorReconstructIndexModel.reconstructIndexed (FIv_NativeArray.value view) n acc := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    rw [take_step view.val n (by omega),model_append,ih (by omega)]
    change SelectorReconstructIndexModel.reconstructIndexed (FIv_NativeArray.value view) n ((acc+acc)+decode (view.val[n]'(by omega)))=
      SelectorReconstructIndexModel.reconstructIndexed (FIv_NativeArray.value view) n ((acc+acc)+FIv_NativeArray.value view n)
    have hread : FIv_NativeArray.value view n=decode (view.val[n]'(by omega)) := by
      unfold FIv_NativeArray.value
      rw [List.getElem?_eq_getElem (by omega)]
    rw [hread]
#print axioms take_step
#print axioms model_append
#print axioms value
end AspisR1.FIx_ReconstructPrefixModel
end
