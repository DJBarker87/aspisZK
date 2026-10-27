import R1Z.PV_Src_PortEnumerateTrace
import R1Z.BuilderForestStdPort

set_option autoImplicit false
namespace R1Z.PV_Src_PortArrayTrace
open Aeneas Aeneas.Std Result BuilderStdModels BuilderForestStdPort
variable {T : Type}

theorem trace (n : Usize) (xs : List T) :
    FiniteTrace (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T n) xs xs := by
  induction xs with
  | nil => exact .done [] [] rfl
  | cons x xs ih => exact .step (x::xs) xs x xs rfl ih

theorem enumerate (n : Usize) (xs : List T) (count : Usize)
    (bound : count.val+xs.length ≤ 24) :
    FiniteTrace (PV_Src_PortEnumerateTrace.iterator
      (core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator T n))
      ⟨xs,count⟩ (PV_Src_PortEnumerateTrace.pairs xs count) :=
  PV_Src_PortEnumerateTrace.trace _ xs xs (trace n xs) count bound

#print axioms trace
#print axioms enumerate
end R1Z.PV_Src_PortArrayTrace
