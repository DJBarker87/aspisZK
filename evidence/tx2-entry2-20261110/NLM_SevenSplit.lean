import NLM_SevenSnapshots
import NLM_LogLaws
set_option autoImplicit false
noncomputable section
namespace NLM_SevenSplit
open Aeneas Aeneas.Std NLM_Snapshot NLM_SevenSnapshots
/-- The state returned by the prefix is the input to its actual suffix. -/
theorem split (allocation : Site → Result Unit) (xs ys : List Site) (s : NLM_Snapshot.State) :
 NLM_SevenSnapshots.G allocation (xs++ys) s=NJU_Log.bind (NLM_SevenSnapshots.G allocation xs s) (NLM_SevenSnapshots.G allocation ys) := by
 induction xs generalizing s with
 | nil => rfl
 | cons c cs ih =>
   simp only [List.cons_append,NLM_SevenSnapshots.G]
   change NJU_Log.bind (NLM_Snapshot.G s c.account c.lo c.hi (allocation c))
     (fun p=>NLM_SevenSnapshots.G allocation (cs++ys) p.2)=
     NJU_Log.bind (NJU_Log.bind (NLM_Snapshot.G s c.account c.lo c.hi (allocation c))
       (fun p=>NLM_SevenSnapshots.G allocation cs p.2)) (NLM_SevenSnapshots.G allocation ys)
   rw [NLM_LogLaws.assoc]
   congr 1
   funext p
   exact ih p.2
#print split
#print axioms split
end NLM_SevenSplit
