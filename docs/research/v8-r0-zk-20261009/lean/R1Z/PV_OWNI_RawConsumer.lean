import R1Z.PV_OWNI_RawFold
set_option autoImplicit false
namespace R1Z.PV_OWNI_RawConsumer
open Aeneas Aeneas.Std Result PV_OWNI_RawOps

def source (point column : List Q) (width trailing suffix : Nat) : Result (Option Q) := do
 if column.length≠1024 then ok none else
  let entries←PV_RDB2D_SparseWeights.build ops point width trailing suffix
  let sum←PV_RDB2D_SparseFold.source ops.toOps column entries ops.zero
  ok (some sum)

def value (point column : List Q) (width trailing suffix : Nat) : Option Q :=
 if column.length≠1024 then none else
 some ((PV_OWNI_BuildTotal.entries point width trailing suffix).foldl
  (PV_OWNI_RawFold.term column) zero)

/-- Complete value-phase Result on arbitrary raw inputs, once the concrete
scanner's split/suffix bounds are supplied. No canonicality or success premise. -/
theorem result (point column : List Q) (width trailing suffix : Nat)
 (split:width+trailing=10) (hs:suffix<2^trailing) :
 source point column width trailing suffix=ok (value point column width trailing suffix) := by
 by_cases h:column.length≠1024
 · unfold source value
   rw [if_pos h,if_pos h]
 · have len:column.length=1024 := by omega
   unfold source value
   simp only [h,if_false,PV_OWNI_BuildTotal.result,bind_tc_ok,zero_value]
   rw [PV_OWNI_RawFold.result]
   · rfl
   · intro e he
     have hb:=PV_OWNI_Rows.bounded point width trailing suffix split hs e he
     omega
#print axioms result
end R1Z.PV_OWNI_RawConsumer
