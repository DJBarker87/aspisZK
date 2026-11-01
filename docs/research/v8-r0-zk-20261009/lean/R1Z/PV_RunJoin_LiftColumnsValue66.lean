import R1Z.PV_RunJoin_LiftColumnsLoop66
import R1Z.PV_RunJoin_LiftArrayTotal66
import R1Z.PV_RunJoin_CloneQ66
import R1Z.PV_RunJoin_ResultPost
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftColumnsValue66
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
open PV_RunJoin_BackendMRows58 (Columns column)
open PV_RunJoin_LiftArray66 (Row Matrix matrix filled)
open PV_RunJoin_LiftRowValue66 (row)
abbrev Q := aspis_core.field.QM31

def vec (a : Array Q 1024#usize) : Row := ⟨a.val,by rw [a.property];scalar_tac⟩
def tails (p : Nat → Row) (h : Row) (g d : Array Q 1024#usize) : Nat → Row :=
  Function.update (Function.update (Function.update p 26 h) 27 (vec g)) 28 (vec d)

attribute [local irreducible] PV_RunJoin_LiftPayload66.payload row

theorem source (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns)
    (hlen : ∀ l,l<26 → (column columns l).length=1024)
    (h : Row) (g d : Array Q 1024#usize) (out : Matrix)
    (success : @host_semantic.lift_columns (types base) (selected base heap box ops) columns h g d=ok out) :
    ∃ p : Nat → Row, out=matrix (tails (filled p (row columns hlen) 26) h g d) := by
  have clone (a : Array Q 1024#usize) :
      @alloc.slice.Slice.to_vec Q
        (@aspis_core.field.QM31.Insts.CoreCloneClone (types base) (selected base heap box ops))
        (Array.to_slice a)=ok (vec a) := by
    exact PV_RunJoin_CloneQ66.complete base heap box ops (Array.to_slice a)
  unfold host_semantic.lift_columns at success
  obtain ⟨initial,hinitial,success⟩ := PV_RunJoin_ResultPost.bind_eq_ok success
  let p := PV_RunJoin_LiftArrayTotal66.cells initial
  have zero : filled p (row columns hlen) 0=p := by
    funext l
    simp only [filled,Nat.not_lt_zero,if_false]
  have hi : matrix (filled p (row columns hlen) 0)=initial := by
    rw [zero]
    exact PV_RunJoin_LiftArrayTotal66.of_array initial
  have hl := PV_RunJoin_LiftColumnsLoop66.complete base heap box ops columns hlen p 26 0#usize rfl
  simp only [show (0#usize).val=0 from rfl] at hl
  rw [hi] at hl
  rw [hl] at success
  simp only [bind_tc_ok,massert,show 26#usize<29#usize from by decide,if_true] at success
  rw [Array.index_mut_usize,PV_RunJoin_LiftArray66.read _ 26#usize (by decide)] at success
  simp only [bind_tc_ok,Aeneas.Std.uncurry] at success
  rw [PV_RunJoin_LiftArray66.restore _ 26#usize (by decide),
    PV_RunJoin_WeightArrayUpdate47.complete _ 26#usize (by decide),
    PV_RunJoin_LiftArray66.set _ 26#usize (by decide)] at success
  simp only [bind_tc_ok,lift] at success
  rw [clone g] at success
  simp only [bind_tc_ok,massert,show 27#usize<29#usize from by decide,if_true] at success
  rw [Array.index_mut_usize,PV_RunJoin_LiftArray66.read _ 27#usize (by decide)] at success
  simp only [bind_tc_ok,Aeneas.Std.uncurry] at success
  rw [PV_RunJoin_LiftArray66.restore _ 27#usize (by decide),
    PV_RunJoin_WeightArrayUpdate47.complete _ 27#usize (by decide),
    PV_RunJoin_LiftArray66.set _ 27#usize (by decide)] at success
  simp only [bind_tc_ok,lift] at success
  rw [clone d] at success
  simp only [bind_tc_ok,massert,show 28#usize<29#usize from by decide,if_true] at success
  rw [Array.index_mut_usize,PV_RunJoin_LiftArray66.read _ 28#usize (by decide)] at success
  simp only [bind_tc_ok,Aeneas.Std.uncurry] at success
  rw [PV_RunJoin_LiftArray66.restore _ 28#usize (by decide),
    PV_RunJoin_WeightArrayUpdate47.complete _ 28#usize (by decide),
    PV_RunJoin_LiftArray66.set _ 28#usize (by decide)] at success
  exact ⟨p,(Result.ok.inj success).symm⟩

#print axioms vec
#print axioms tails
#print axioms source
end R1Z.PV_RunJoin_LiftColumnsValue66
