import NNG_Factor087
import NNG_FrontErase087
import NNG_Producer087
import NNG_ModelHead136
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PrepareOrigin094
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMT_CallTree
/-- Actual successful prepare exposes its SAME front result and final
Prepared call. Neither result is selected independently of that execution. -/
theorem returned (env : RSL.Env) (s : Parent Unit Unit) (p : verifier.Prepared) (g : Scratch)
 (native : NMP_Emitted.prepare (NNG_PrepareEmission087.calls env) s=.ok (.Ok p,g)) :
 ∃ sem v,NNG_FrontValue087.tree (NNG_PrepareEmission087.calls env) s=.ok (.Ok (sem,v)) ∧
 NNG_PreparedCall087.call s.digest sem v s.hash s.scratch=.ok (.Ok p,g) := by
 rw [←NNG_Producer087.source env s,←NNG_Factor087.tree,erase_bind,NNG_FrontErase087.tree] at native
 obtain ⟨reply,front,tail⟩ := NNG_ModelSuccess136.bind_out _ _ _ native
 cases reply with
 | Err e=>cases tail
 | Ok pair=>
   rcases pair with ⟨sem,v⟩
   refine ⟨sem,v,front,?_⟩
   unfold NNG_Factor087.finish NNG_Tree087.mark NNG_Tree087.prepared at tail
   simp only [Bind.bind,erase_bind,erase_invoke,NNG_PrepareEmission087.calls,bind_tc_ok] at tail
   exact tail
#print axioms returned
end AspisR1.NNG_PrepareOrigin094
