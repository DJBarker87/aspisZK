import NDO_JGm_TX2_BinarySelect
import NDO_JGm_TX2_Supplied
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGm_TX2_RowControl
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem step {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s t : reference.Scratch) (nodes : Slice U8) (i w ni nw : Usize)
    (active : i<s.n)
    (run : reference.binary_step D hash s nodes i w=ok (.Next t ni nw)) :
    reference.level_rows D hash s nodes i w=reference.level_rows D hash t nodes ni nw := by
  rw [reference.level_rows,if_neg (by change ¬i.val≥s.n.val; change i.val<s.n.val at active;omega),run]
  rfl
#print axioms step

theorem done {Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (s : reference.Scratch) (nodes : Slice U8) (i w : Usize) (finished : s.n ≤ i) :
    reference.level_rows D hash s nodes i w=ok (.Done {s with n:=w}) := by
  rw [reference.level_rows,if_pos finished]
#print axioms done
end AspisR1.JGm_TX2_RowControl
end
