import NJP_LoopModel

set_option autoImplicit false
noncomputable section
namespace NJP_LoopBind
open Aeneas Aeneas.Std Result NJP_RowModel NJP_LoopModel
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem returned {α β : Type} (H : Request → Digest)
    (p : Program Request Digest (Result α)) (f : α → Program Request Digest (Result β))
    (history : List (Request × Digest)) (x : α) (same : eval H p=(history,ok x)) :
 eval H (bindRun p f)=(history++(eval H (f x)).1,(eval H (f x)).2) := by
 simp only [bindRun,eval_bind,same]

/-- A stopped row retains its entire partial scratch and its exact issued
request prefix; the level does not invoke the next row. -/
theorem stopped_row (H : Request → Digest) (nodes : Nat → U8) (length fuel : Nat)
    (s stopped : Scratch) (i w : Nat) (active : ¬s.n ≤ i)
    (history : List (Request × Digest))
    (stopped_at : eval H (node nodes length s i w)=(history,ok (.stop stopped))) :
 eval H (rows nodes length (fuel+1) s i w)=(history,ok (.stop stopped)) := by
 rw [rows,if_neg active,returned H _ _ history _ stopped_at]
 simp only [eval,List.append_nil]

/-- A stopped height retains the same prefix, with no later height executed. -/
theorem stopped_level (H : Request → Digest) (nodes : Nat → U8) (length height : Nat)
    (s stopped : Scratch) (history : List (Request × Digest))
    (stopped_at : eval H (level nodes length s)=(history,ok (.stop stopped))) :
 eval H (levels nodes length (height+1) s)=(history,ok (.stop stopped)) := by
 rw [levels,returned H _ _ history _ stopped_at]
 simp only [eval,List.append_nil]

#print returned
#print axioms returned
#print stopped_row
#print axioms stopped_row
#print stopped_level
#print axioms stopped_level
end NJP_LoopBind
end
