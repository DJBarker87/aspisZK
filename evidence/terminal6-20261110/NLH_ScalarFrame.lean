import NLH_ScalarDefs
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_ScalarFrame
open FIq_Native NLH_ScalarDefs
open NKR_TermScalarInvocation (Packet)
/-- Full twelve-local frame for one native statement: future SSA slots are
retained and no previous operand is replaced by a freely chosen endpoint. -/
theorem update {pub o s before} (p : Packet pub o s before) (i : Fin 12) :
 (fun j => if j=i then values p i else snapshot p i.val j)=snapshot p (i.val+1) := by
 funext j
 by_cases same : j=i
 · subst j
   simp only [snapshot,if_pos (Nat.lt_succ_self i.val),ite_true]
 · have different : j.val ≠ i.val := by intro h;exact same (Fin.ext h)
   unfold snapshot
   by_cases earlier : j.val < i.val
   · simp only [if_pos earlier,if_neg same,if_pos (show j.val < i.val+1 by omega)]
   · simp only [if_neg earlier,if_neg same,if_neg (show ¬j.val < i.val+1 by omega)]
#print axioms update
end AspisR1.NLH_ScalarFrame
end
