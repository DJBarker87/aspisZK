import R1Z.PV_RunJoin_LiftCell63
import R1Z.ProverRw19LoopBind
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_LiftRow63
open Aeneas Aeneas.Std Result ProverRwFull PV_RunJoin_WeightInstalled46
abbrev Columns := Array (alloc.vec.Vec aspis_core.field.M31) 26#usize
abbrev Q := aspis_core.field.QM31

def step (columns : Columns) (lane : Usize) (out : alloc.vec.Vec Q) (row : Usize) : Result (alloc.vec.Vec Q) := do
  let column ← Array.index_usize columns lane
  let m ← alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice aspis_core.field.M31) column row
  alloc.vec.Vec.push out (PV_RunJoin_LiftCell63.lifted m)

def phase (columns : Columns) (lane : Usize) : Nat → alloc.vec.Vec Q → Usize → Result (alloc.vec.Vec Q)
  | 0,out,_ => ok out
  | n+1,out,row => do
      let next ← step columns lane out row
      phase columns lane n next (Usize.wrapping_add row 1#usize)

attribute [local irreducible] selected PV_B2_F_RawNative.selected PV_B2_F_ResourceFamilies.selected

theorem one_step (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns) (lane : Usize)
    (out : alloc.vec.Vec Q) (row : Usize) (more : row<1024#usize) :
    @host_semantic.lift_columns_loop0_loop0.body (types base) (selected base heap box ops) columns lane out row=
      (do let next ← step columns lane out row
          ok (.cont (next,Usize.wrapping_add row 1#usize))) := by
  simp only [host_semantic.lift_columns_loop0_loop0.body,more,if_true,step,lift,bind_tc_ok,bind_assoc_eq]
  apply congrArg (Aeneas.Std.bind _)
  funext column
  apply congrArg (Aeneas.Std.bind _)
  funext m
  rw [PV_RunJoin_LiftCell63.complete base heap box ops m]
  simp only [bind_tc_ok]

theorem complete (base : ExternalTypes) (heap : Heap) (box : Box)
    (ops : @ExternalFuns (types base)) (columns : Columns) (lane : Usize)
    (n : Nat) (out : alloc.vec.Vec Q) (row : Usize) (rank : row.val+n=1024) :
    @host_semantic.lift_columns_loop0_loop0 (types base) (selected base heap box ops) columns lane out row=
      phase columns lane n out row := by
  induction n generalizing row out with
  | zero =>
    have stop : ¬ row<1024#usize := by change ¬row.val<1024;omega
    unfold host_semantic.lift_columns_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    simp only [host_semantic.lift_columns_loop0_loop0.body,stop,if_false,bind_tc_ok,phase]
  | succ n ih =>
    have more : row<1024#usize := by change row.val<1024;omega
    have next := ProverCommitPairCounter47.next_val row more
    unfold host_semantic.lift_columns_loop0_loop0
    rw [ProverRw19LoopBind.loop_bind]
    dsimp only
    rw [one_step base heap box ops columns lane out row more]
    simp only [bind_assoc_eq,bind_tc_ok,phase]
    apply congrArg (Aeneas.Std.bind _)
    funext out'
    change @host_semantic.lift_columns_loop0_loop0 (types base) (selected base heap box ops)
      columns lane out' (Usize.wrapping_add row 1#usize)=_
    exact ih out' (Usize.wrapping_add row 1#usize) (by rw [next];omega)

#print axioms step
#print axioms phase
#print axioms one_step
#print axioms complete
end R1Z.PV_RunJoin_LiftRow63
