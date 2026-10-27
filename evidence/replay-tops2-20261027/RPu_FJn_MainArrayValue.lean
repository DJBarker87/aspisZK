import RPu_FIr_ArrayRead
import RPt_FIp_SemanticValues
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJn_MainArrayValue
open Aeneas Aeneas.Std Result
open FIp_SemanticArithmetic (MQ)
open FIp_SemanticValues (Canon decode)
def value {N : Usize} (a : Array MQ N) (i : Nat) :=
  match a.val[i]? with | none=>0 | some q=>decode q
theorem read {N : Usize} (a : Array MQ N) (i : Usize) (q : MQ)
    (run : Array.index_usize a i=ok q) : value a i.val=decode q := by
  simp only [value,FIr_ArrayRead.slot a i q run]
theorem canonical {N : Usize} (a : Array MQ N) (i : Usize) (q : MQ)
    (all : ∀ x∈a.val,Canon x) (run : Array.index_usize a i=ok q) : Canon q :=
  all q (FIr_ArrayRead.member a i q run)
#print axioms read
#print axioms canonical
end AspisR1.FJn_MainArrayValue
end
