import S1ClosedPreparationHashCodeV1
set_option autoImplicit false
namespace AspisR1.JGg_QueryTrace
open Aeneas Aeneas.Std Result

theorem read (q : Array U32 22#usize) (i : Usize) (bound : i.val<22) :
    Array.index_usize q i=ok (q.val[i.val]'(by rw [q.property];exact bound)) := by
  obtain ⟨out,call,same⟩ := WP.spec_imp_exists
    (Array.index_usize_spec q i (by rw [q.property];exact bound))
  exact call.trans (congrArg Result.ok same)
#print axioms read
end AspisR1.JGg_QueryTrace
