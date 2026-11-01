import R1Z.PV_RunJoin_BackendMRows58
import R1Z.PV_RunJoin_WeightArrayUpdate47
import R1Z.PV_RunJoin_WeightBorrow46
set_option autoImplicit false
namespace R1Z.PV_RunJoin_LiftArray66
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Q := aspis_core.field.QM31
abbrev Row := alloc.vec.Vec Q
abbrev Matrix := Array Row 29#usize

def matrix (p : Nat → Row) : Matrix := ProverCommitArray49.array 29#usize p
def filled (p input : Nat → Row) (stop : Nat) (lane : Nat) : Row :=
  if lane<stop then input lane else p lane

theorem read (p : Nat → Row) (i : Usize) (hi : i.val<29) :
    Array.index_usize (matrix p) i=ok (p i.val) :=
  ProverCommitArray49.index 29#usize p i hi

theorem set (p : Nat → Row) (i : Usize) (hi : i.val<29) (value : Row) :
    Aeneas.Std.Array.set (matrix p) i value=matrix (Function.update p i.val value) := by
  apply Subtype.ext
  change (List.ofFn (fun j : Fin 29 => p j.val)).set i.val value=_
  apply List.ext_getElem
  · simp only [matrix,ProverCommitArray49.array,List.length_set,List.length_ofFn,UScalar.ofNatCore_val_eq]
  · intro j hj hj'
    simp only [matrix,ProverCommitArray49.array,List.getElem_set,List.getElem_ofFn]
    by_cases he : j=i.val
    · subst j
      simp only [Function.update_self,if_true]
    · simp only [he,Ne.symm he,if_false,Function.update_of_ne he]

theorem restore (p : Nat → Row) (i : Usize) (hi : i.val<29) :
    Aeneas.Std.Array.set (matrix p) i (p i.val)=matrix p := by
  apply Subtype.ext
  apply PV_RunJoin_WeightFactorRestore47.list_restore
  exact PV_RunJoin_WeightFactorRestore47.read_value _ _ _ (read p i hi)

theorem step (p input : Nat → Row) (lane : Usize) (hi : lane.val<29) :
    Aeneas.Std.Array.set (matrix (filled p input lane.val)) lane (input lane.val)=
      matrix (filled p input (lane.val+1)) := by
  rw [set _ lane hi]
  apply congrArg matrix
  funext l
  by_cases eq : l=lane.val
  · subst l
    simp only [Function.update_self,filled,Nat.lt_succ_self,if_true]
  · rw [Function.update_of_ne eq]
    unfold filled
    by_cases before : l<lane.val
    · simp only [if_pos before,if_pos (show l<lane.val+1 from by omega)]
    · simp only [if_neg before,if_neg (show ¬l<lane.val+1 from by omega)]

#print axioms matrix
#print axioms filled
#print axioms read
#print axioms set
#print axioms restore
#print axioms step
end R1Z.PV_RunJoin_LiftArray66
