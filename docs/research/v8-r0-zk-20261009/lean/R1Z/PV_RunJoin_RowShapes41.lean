import R1Z.PV_RunJoin_SemanticDomain40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_RowShapes41
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

theorem row0 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 0#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row0

theorem row1 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 1#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row1

theorem row2 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 2#u8 =
      .ok (some (1#u8,32#usize)) := by
  rfl
#print axioms row2

theorem row3 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 3#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row3

theorem row4 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 4#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row4

theorem row5 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 5#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row5

theorem row6 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 6#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row6

theorem row7 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 7#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row7

theorem row8 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 8#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row8

theorem row9 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 9#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row9

theorem row10 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 10#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row10

theorem row11 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 11#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row11

theorem row12 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 12#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row12

theorem row13 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 13#u8 =
      .ok (some (0#u8,0#usize)) := by
  rfl
#print axioms row13

theorem row14 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 14#u8 =
      .ok (some (3#u8,32#usize)) := by
  rfl
#print axioms row14

theorem row15 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 15#u8 =
      .ok (some (2#u8,896#usize)) := by
  change Result.ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize)) =
    Result.ok (some (2#u8,896#usize))
  congr 3
  scalar_tac
#print axioms row15

theorem row16 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 16#u8 =
      .ok (some (2#u8,896#usize)) := by
  change Result.ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize)) =
    Result.ok (some (2#u8,896#usize))
  congr 3
  scalar_tac
#print axioms row16

theorem row17 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 17#u8 =
      .ok (some (2#u8,896#usize)) := by
  change Result.ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize)) =
    Result.ok (some (2#u8,896#usize))
  congr 3
  scalar_tac
#print axioms row17

theorem row18 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 18#u8 =
      .ok (some (2#u8,896#usize)) := by
  change Result.ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize)) =
    Result.ok (some (2#u8,896#usize))
  congr 3
  scalar_tac
#print axioms row18

theorem row19 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 19#u8 =
      .ok (some (2#u8,896#usize)) := by
  change Result.ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize)) =
    Result.ok (some (2#u8,896#usize))
  congr 3
  scalar_tac
#print axioms row19

theorem row20 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 20#u8 =
      .ok (some (2#u8,896#usize)) := by
  change Result.ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize)) =
    Result.ok (some (2#u8,896#usize))
  congr 3
  scalar_tac
#print axioms row20

theorem row21 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 21#u8 =
      .ok (some (2#u8,896#usize)) := by
  change Result.ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize)) =
    Result.ok (some (2#u8,896#usize))
  congr 3
  scalar_tac
#print axioms row21

theorem row22 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 22#u8 =
      .ok (some (2#u8,896#usize)) := by
  change Result.ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize)) =
    Result.ok (some (2#u8,896#usize))
  congr 3
  scalar_tac
#print axioms row22

theorem row23 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 23#u8 =
      .ok (some (2#u8,896#usize)) := by
  change Result.ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize)) =
    Result.ok (some (2#u8,896#usize))
  congr 3
  scalar_tac
#print axioms row23

theorem row24 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 24#u8 =
      .ok (some (2#u8,896#usize)) := by
  change Result.ok (some (2#u8,Usize.wrapping_mul 28#usize 32#usize)) =
    Result.ok (some (2#u8,896#usize))
  congr 3
  scalar_tac
#print axioms row24

theorem row25 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 25#u8 =
      .ok (some (4#u8,3712#usize)) := by
  change Result.ok (some (4#u8,Usize.wrapping_mul (Usize.wrapping_add 87#usize 29#usize) 32#usize)) =
    Result.ok (some (4#u8,3712#usize))
  congr 3
  scalar_tac
#print axioms row25

theorem row26 (ops : ExternalFuns) :
    @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) 26#u8 =
      .ok (some (5#u8,928#usize)) := by
  change Result.ok (some (5#u8,Usize.wrapping_mul 29#usize 32#usize)) =
    Result.ok (some (5#u8,928#usize))
  congr 3
  scalar_tac
#print axioms row26
end R1Z.PV_RunJoin_RowShapes41
