import PV_B3P_Carrier227
import PV_B3P_P227_14
namespace PV_B3P_Install227
open Aeneas Aeneas.Std ProverRwFull
set_option autoImplicit false
abbrev Types := PV_B3P_Carrier227.Types
abbrev SourceQ := PV_B3P_227.aspis_core.field.QM31
abbrev SourceError := PV_B3P_227.aspis_core.state_only_prefix.r0.Error
abbrev Terminal := PV_B3P_227.reference_terminal.SemanticPublic →
  Array (Array SourceQ 29#usize) 3#usize → Array SourceQ 10#usize →
  PV_B3P_227.aspis_core.state_only_prefix.r0.Challenges →
  Result (core.result.Result SourceQ SourceError)

def transport (r : Result (core.result.Result SourceQ SourceError)) :
    Result (core.result.Result ProverRwFull.aspis_core.field.QM31 SourceError) :=
  match r with
  | .ok (.Ok value) => .ok (.Ok (PV_B3P_Carrier227.fromQ value))
  | .ok (.Err e) => .ok (.Err e)
  | .fail e => .fail e
  | .div => .div

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) : @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {ops with op227 := fun p claims point c => transport (terminal
    (PV_B3P_Carrier227.semantic base p)
    (PV_B3P_Carrier227.mapArray (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ) claims)
    (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ point)
    (PV_B3P_Carrier227.challenges c))}

theorem source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal)
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base))
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (c : aspis_core.state_only_prefix.r0.Challenges) :
    @ExternalFuns.op227 (Types base) (selected base ops terminal) p claims point c =
      transport (terminal (PV_B3P_Carrier227.semantic base p)
        (PV_B3P_Carrier227.mapArray (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ) claims)
        (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ point)
        (PV_B3P_Carrier227.challenges c)) := rfl

/-- A closed installation of the checked emitted reference, with no callback
parameter left in the installed operation. Native structural correspondence and
successful nonvacuity remain separate obligations. -/
@[reducible] def actual (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  selected base ops PV_B3P_227.reference_terminal.reference227

theorem actual_source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base))
    (claims : Array (Array aspis_core.field.QM31 29#usize) 3#usize)
    (point : Array aspis_core.field.QM31 10#usize)
    (c : aspis_core.state_only_prefix.r0.Challenges) :
    @ExternalFuns.op227 (Types base) (actual base ops) p claims point c =
      transport (PV_B3P_227.reference_terminal.reference227
        (PV_B3P_Carrier227.semantic base p)
        (PV_B3P_Carrier227.mapArray (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ) claims)
        (PV_B3P_Carrier227.mapArray PV_B3P_Carrier227.toQ point)
        (PV_B3P_Carrier227.challenges c)) := rfl

#print axioms actual_source

theorem error_tag (e : SourceError) : transport (.ok (.Err e)) = .ok (.Err e) := rfl
theorem fail_tag (e : Aeneas.Std.Error) : transport (.fail e) = .fail e := rfl
theorem div_tag : transport .div = .div := rfl

#print axioms source
#print axioms error_tag
#print axioms fail_tag
#print axioms div_tag

theorem preserved_op0 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op0 (Types base) (selected base ops terminal) =
      @ExternalFuns.op0 (Types base) ops := rfl
#print axioms preserved_op0

theorem preserved_op1 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op1 (Types base) (selected base ops terminal) =
      @ExternalFuns.op1 (Types base) ops := rfl
#print axioms preserved_op1

theorem preserved_op2 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op2 (Types base) (selected base ops terminal) =
      @ExternalFuns.op2 (Types base) ops := rfl
#print axioms preserved_op2

theorem preserved_op3 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op3 (Types base) (selected base ops terminal) =
      @ExternalFuns.op3 (Types base) ops := rfl
#print axioms preserved_op3

theorem preserved_op4 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op4 (Types base) (selected base ops terminal) =
      @ExternalFuns.op4 (Types base) ops := rfl
#print axioms preserved_op4

theorem preserved_op5 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op5 (Types base) (selected base ops terminal) =
      @ExternalFuns.op5 (Types base) ops := rfl
#print axioms preserved_op5

theorem preserved_op6 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op6 (Types base) (selected base ops terminal) =
      @ExternalFuns.op6 (Types base) ops := rfl
#print axioms preserved_op6

theorem preserved_op7 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op7 (Types base) (selected base ops terminal) =
      @ExternalFuns.op7 (Types base) ops := rfl
#print axioms preserved_op7

theorem preserved_op8 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op8 (Types base) (selected base ops terminal) =
      @ExternalFuns.op8 (Types base) ops := rfl
#print axioms preserved_op8

theorem preserved_op9 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op9 (Types base) (selected base ops terminal) =
      @ExternalFuns.op9 (Types base) ops := rfl
#print axioms preserved_op9

theorem preserved_op10 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op10 (Types base) (selected base ops terminal) =
      @ExternalFuns.op10 (Types base) ops := rfl
#print axioms preserved_op10

theorem preserved_op11 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op11 (Types base) (selected base ops terminal) =
      @ExternalFuns.op11 (Types base) ops := rfl
#print axioms preserved_op11

theorem preserved_op12 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op12 (Types base) (selected base ops terminal) =
      @ExternalFuns.op12 (Types base) ops := rfl
#print axioms preserved_op12

theorem preserved_op13 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op13 (Types base) (selected base ops terminal) =
      @ExternalFuns.op13 (Types base) ops := rfl
#print axioms preserved_op13

theorem preserved_op14 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op14 (Types base) (selected base ops terminal) =
      @ExternalFuns.op14 (Types base) ops := rfl
#print axioms preserved_op14

theorem preserved_op15 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op15 (Types base) (selected base ops terminal) =
      @ExternalFuns.op15 (Types base) ops := rfl
#print axioms preserved_op15

theorem preserved_op16 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op16 (Types base) (selected base ops terminal) =
      @ExternalFuns.op16 (Types base) ops := rfl
#print axioms preserved_op16

theorem preserved_op17 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op17 (Types base) (selected base ops terminal) =
      @ExternalFuns.op17 (Types base) ops := rfl
#print axioms preserved_op17

theorem preserved_op18 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op18 (Types base) (selected base ops terminal) =
      @ExternalFuns.op18 (Types base) ops := rfl
#print axioms preserved_op18

theorem preserved_op19 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op19 (Types base) (selected base ops terminal) =
      @ExternalFuns.op19 (Types base) ops := rfl
#print axioms preserved_op19

theorem preserved_op20 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op20 (Types base) (selected base ops terminal) =
      @ExternalFuns.op20 (Types base) ops := rfl
#print axioms preserved_op20

theorem preserved_op21 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op21 (Types base) (selected base ops terminal) =
      @ExternalFuns.op21 (Types base) ops := rfl
#print axioms preserved_op21

theorem preserved_op22 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op22 (Types base) (selected base ops terminal) =
      @ExternalFuns.op22 (Types base) ops := rfl
#print axioms preserved_op22

theorem preserved_op23 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op23 (Types base) (selected base ops terminal) =
      @ExternalFuns.op23 (Types base) ops := rfl
#print axioms preserved_op23

theorem preserved_op24 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op24 (Types base) (selected base ops terminal) =
      @ExternalFuns.op24 (Types base) ops := rfl
#print axioms preserved_op24

theorem preserved_op25 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op25 (Types base) (selected base ops terminal) =
      @ExternalFuns.op25 (Types base) ops := rfl
#print axioms preserved_op25

theorem preserved_op26 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op26 (Types base) (selected base ops terminal) =
      @ExternalFuns.op26 (Types base) ops := rfl
#print axioms preserved_op26

theorem preserved_op27 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op27 (Types base) (selected base ops terminal) =
      @ExternalFuns.op27 (Types base) ops := rfl
#print axioms preserved_op27

theorem preserved_op28 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op28 (Types base) (selected base ops terminal) =
      @ExternalFuns.op28 (Types base) ops := rfl
#print axioms preserved_op28

theorem preserved_op29 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op29 (Types base) (selected base ops terminal) =
      @ExternalFuns.op29 (Types base) ops := rfl
#print axioms preserved_op29

theorem preserved_op30 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op30 (Types base) (selected base ops terminal) =
      @ExternalFuns.op30 (Types base) ops := rfl
#print axioms preserved_op30

theorem preserved_op31 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op31 (Types base) (selected base ops terminal) =
      @ExternalFuns.op31 (Types base) ops := rfl
#print axioms preserved_op31

theorem preserved_op32 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op32 (Types base) (selected base ops terminal) =
      @ExternalFuns.op32 (Types base) ops := rfl
#print axioms preserved_op32

theorem preserved_op33 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op33 (Types base) (selected base ops terminal) =
      @ExternalFuns.op33 (Types base) ops := rfl
#print axioms preserved_op33

theorem preserved_op34 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op34 (Types base) (selected base ops terminal) =
      @ExternalFuns.op34 (Types base) ops := rfl
#print axioms preserved_op34

theorem preserved_op35 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op35 (Types base) (selected base ops terminal) =
      @ExternalFuns.op35 (Types base) ops := rfl
#print axioms preserved_op35

theorem preserved_op36 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op36 (Types base) (selected base ops terminal) =
      @ExternalFuns.op36 (Types base) ops := rfl
#print axioms preserved_op36

theorem preserved_op37 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op37 (Types base) (selected base ops terminal) =
      @ExternalFuns.op37 (Types base) ops := rfl
#print axioms preserved_op37

theorem preserved_op38 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op38 (Types base) (selected base ops terminal) =
      @ExternalFuns.op38 (Types base) ops := rfl
#print axioms preserved_op38

theorem preserved_op39 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op39 (Types base) (selected base ops terminal) =
      @ExternalFuns.op39 (Types base) ops := rfl
#print axioms preserved_op39

theorem preserved_op40 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op40 (Types base) (selected base ops terminal) =
      @ExternalFuns.op40 (Types base) ops := rfl
#print axioms preserved_op40

theorem preserved_op41 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op41 (Types base) (selected base ops terminal) =
      @ExternalFuns.op41 (Types base) ops := rfl
#print axioms preserved_op41

theorem preserved_op42 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op42 (Types base) (selected base ops terminal) =
      @ExternalFuns.op42 (Types base) ops := rfl
#print axioms preserved_op42

theorem preserved_op43 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op43 (Types base) (selected base ops terminal) =
      @ExternalFuns.op43 (Types base) ops := rfl
#print axioms preserved_op43

theorem preserved_op44 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op44 (Types base) (selected base ops terminal) =
      @ExternalFuns.op44 (Types base) ops := rfl
#print axioms preserved_op44

theorem preserved_op45 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op45 (Types base) (selected base ops terminal) =
      @ExternalFuns.op45 (Types base) ops := rfl
#print axioms preserved_op45

theorem preserved_op46 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op46 (Types base) (selected base ops terminal) =
      @ExternalFuns.op46 (Types base) ops := rfl
#print axioms preserved_op46

theorem preserved_op47 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op47 (Types base) (selected base ops terminal) =
      @ExternalFuns.op47 (Types base) ops := rfl
#print axioms preserved_op47

theorem preserved_op48 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op48 (Types base) (selected base ops terminal) =
      @ExternalFuns.op48 (Types base) ops := rfl
#print axioms preserved_op48

theorem preserved_op49 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op49 (Types base) (selected base ops terminal) =
      @ExternalFuns.op49 (Types base) ops := rfl
#print axioms preserved_op49

theorem preserved_op50 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op50 (Types base) (selected base ops terminal) =
      @ExternalFuns.op50 (Types base) ops := rfl
#print axioms preserved_op50

theorem preserved_op51 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op51 (Types base) (selected base ops terminal) =
      @ExternalFuns.op51 (Types base) ops := rfl
#print axioms preserved_op51

theorem preserved_op52 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op52 (Types base) (selected base ops terminal) =
      @ExternalFuns.op52 (Types base) ops := rfl
#print axioms preserved_op52

theorem preserved_op53 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op53 (Types base) (selected base ops terminal) =
      @ExternalFuns.op53 (Types base) ops := rfl
#print axioms preserved_op53

theorem preserved_op54 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op54 (Types base) (selected base ops terminal) =
      @ExternalFuns.op54 (Types base) ops := rfl
#print axioms preserved_op54

theorem preserved_op55 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op55 (Types base) (selected base ops terminal) =
      @ExternalFuns.op55 (Types base) ops := rfl
#print axioms preserved_op55

theorem preserved_op56 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op56 (Types base) (selected base ops terminal) =
      @ExternalFuns.op56 (Types base) ops := rfl
#print axioms preserved_op56

theorem preserved_op57 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op57 (Types base) (selected base ops terminal) =
      @ExternalFuns.op57 (Types base) ops := rfl
#print axioms preserved_op57

theorem preserved_op58 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op58 (Types base) (selected base ops terminal) =
      @ExternalFuns.op58 (Types base) ops := rfl
#print axioms preserved_op58

theorem preserved_op59 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op59 (Types base) (selected base ops terminal) =
      @ExternalFuns.op59 (Types base) ops := rfl
#print axioms preserved_op59

theorem preserved_op60 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op60 (Types base) (selected base ops terminal) =
      @ExternalFuns.op60 (Types base) ops := rfl
#print axioms preserved_op60

theorem preserved_op61 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op61 (Types base) (selected base ops terminal) =
      @ExternalFuns.op61 (Types base) ops := rfl
#print axioms preserved_op61

theorem preserved_op62 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op62 (Types base) (selected base ops terminal) =
      @ExternalFuns.op62 (Types base) ops := rfl
#print axioms preserved_op62

theorem preserved_op63 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op63 (Types base) (selected base ops terminal) =
      @ExternalFuns.op63 (Types base) ops := rfl
#print axioms preserved_op63

theorem preserved_op64 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op64 (Types base) (selected base ops terminal) =
      @ExternalFuns.op64 (Types base) ops := rfl
#print axioms preserved_op64

theorem preserved_op65 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op65 (Types base) (selected base ops terminal) =
      @ExternalFuns.op65 (Types base) ops := rfl
#print axioms preserved_op65

theorem preserved_op66 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op66 (Types base) (selected base ops terminal) =
      @ExternalFuns.op66 (Types base) ops := rfl
#print axioms preserved_op66

theorem preserved_op67 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op67 (Types base) (selected base ops terminal) =
      @ExternalFuns.op67 (Types base) ops := rfl
#print axioms preserved_op67

theorem preserved_op68 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op68 (Types base) (selected base ops terminal) =
      @ExternalFuns.op68 (Types base) ops := rfl
#print axioms preserved_op68

theorem preserved_op69 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op69 (Types base) (selected base ops terminal) =
      @ExternalFuns.op69 (Types base) ops := rfl
#print axioms preserved_op69

theorem preserved_op70 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op70 (Types base) (selected base ops terminal) =
      @ExternalFuns.op70 (Types base) ops := rfl
#print axioms preserved_op70

theorem preserved_op71 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op71 (Types base) (selected base ops terminal) =
      @ExternalFuns.op71 (Types base) ops := rfl
#print axioms preserved_op71

theorem preserved_op72 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op72 (Types base) (selected base ops terminal) =
      @ExternalFuns.op72 (Types base) ops := rfl
#print axioms preserved_op72

theorem preserved_op73 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op73 (Types base) (selected base ops terminal) =
      @ExternalFuns.op73 (Types base) ops := rfl
#print axioms preserved_op73

theorem preserved_op74 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op74 (Types base) (selected base ops terminal) =
      @ExternalFuns.op74 (Types base) ops := rfl
#print axioms preserved_op74

theorem preserved_op75 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op75 (Types base) (selected base ops terminal) =
      @ExternalFuns.op75 (Types base) ops := rfl
#print axioms preserved_op75

theorem preserved_op76 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op76 (Types base) (selected base ops terminal) =
      @ExternalFuns.op76 (Types base) ops := rfl
#print axioms preserved_op76

theorem preserved_op77 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op77 (Types base) (selected base ops terminal) =
      @ExternalFuns.op77 (Types base) ops := rfl
#print axioms preserved_op77

theorem preserved_op78 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op78 (Types base) (selected base ops terminal) =
      @ExternalFuns.op78 (Types base) ops := rfl
#print axioms preserved_op78

theorem preserved_op79 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op79 (Types base) (selected base ops terminal) =
      @ExternalFuns.op79 (Types base) ops := rfl
#print axioms preserved_op79

theorem preserved_op80 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op80 (Types base) (selected base ops terminal) =
      @ExternalFuns.op80 (Types base) ops := rfl
#print axioms preserved_op80

theorem preserved_op81 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op81 (Types base) (selected base ops terminal) =
      @ExternalFuns.op81 (Types base) ops := rfl
#print axioms preserved_op81

theorem preserved_op82 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op82 (Types base) (selected base ops terminal) =
      @ExternalFuns.op82 (Types base) ops := rfl
#print axioms preserved_op82

theorem preserved_op83 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op83 (Types base) (selected base ops terminal) =
      @ExternalFuns.op83 (Types base) ops := rfl
#print axioms preserved_op83

theorem preserved_op84 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op84 (Types base) (selected base ops terminal) =
      @ExternalFuns.op84 (Types base) ops := rfl
#print axioms preserved_op84

theorem preserved_op85 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op85 (Types base) (selected base ops terminal) =
      @ExternalFuns.op85 (Types base) ops := rfl
#print axioms preserved_op85

theorem preserved_op86 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op86 (Types base) (selected base ops terminal) =
      @ExternalFuns.op86 (Types base) ops := rfl
#print axioms preserved_op86

theorem preserved_op87 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op87 (Types base) (selected base ops terminal) =
      @ExternalFuns.op87 (Types base) ops := rfl
#print axioms preserved_op87

theorem preserved_op88 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op88 (Types base) (selected base ops terminal) =
      @ExternalFuns.op88 (Types base) ops := rfl
#print axioms preserved_op88

theorem preserved_op89 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op89 (Types base) (selected base ops terminal) =
      @ExternalFuns.op89 (Types base) ops := rfl
#print axioms preserved_op89

theorem preserved_op90 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op90 (Types base) (selected base ops terminal) =
      @ExternalFuns.op90 (Types base) ops := rfl
#print axioms preserved_op90

theorem preserved_op91 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op91 (Types base) (selected base ops terminal) =
      @ExternalFuns.op91 (Types base) ops := rfl
#print axioms preserved_op91

theorem preserved_op92 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op92 (Types base) (selected base ops terminal) =
      @ExternalFuns.op92 (Types base) ops := rfl
#print axioms preserved_op92

theorem preserved_op93 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op93 (Types base) (selected base ops terminal) =
      @ExternalFuns.op93 (Types base) ops := rfl
#print axioms preserved_op93

theorem preserved_op94 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op94 (Types base) (selected base ops terminal) =
      @ExternalFuns.op94 (Types base) ops := rfl
#print axioms preserved_op94

theorem preserved_op95 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op95 (Types base) (selected base ops terminal) =
      @ExternalFuns.op95 (Types base) ops := rfl
#print axioms preserved_op95

theorem preserved_op96 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op96 (Types base) (selected base ops terminal) =
      @ExternalFuns.op96 (Types base) ops := rfl
#print axioms preserved_op96

theorem preserved_op97 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op97 (Types base) (selected base ops terminal) =
      @ExternalFuns.op97 (Types base) ops := rfl
#print axioms preserved_op97

theorem preserved_op98 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op98 (Types base) (selected base ops terminal) =
      @ExternalFuns.op98 (Types base) ops := rfl
#print axioms preserved_op98

theorem preserved_op99 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op99 (Types base) (selected base ops terminal) =
      @ExternalFuns.op99 (Types base) ops := rfl
#print axioms preserved_op99

theorem preserved_op100 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op100 (Types base) (selected base ops terminal) =
      @ExternalFuns.op100 (Types base) ops := rfl
#print axioms preserved_op100

theorem preserved_op101 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op101 (Types base) (selected base ops terminal) =
      @ExternalFuns.op101 (Types base) ops := rfl
#print axioms preserved_op101

theorem preserved_op102 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op102 (Types base) (selected base ops terminal) =
      @ExternalFuns.op102 (Types base) ops := rfl
#print axioms preserved_op102

theorem preserved_op103 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op103 (Types base) (selected base ops terminal) =
      @ExternalFuns.op103 (Types base) ops := rfl
#print axioms preserved_op103

theorem preserved_op104 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op104 (Types base) (selected base ops terminal) =
      @ExternalFuns.op104 (Types base) ops := rfl
#print axioms preserved_op104

theorem preserved_op105 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op105 (Types base) (selected base ops terminal) =
      @ExternalFuns.op105 (Types base) ops := rfl
#print axioms preserved_op105

theorem preserved_op106 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op106 (Types base) (selected base ops terminal) =
      @ExternalFuns.op106 (Types base) ops := rfl
#print axioms preserved_op106

theorem preserved_op107 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op107 (Types base) (selected base ops terminal) =
      @ExternalFuns.op107 (Types base) ops := rfl
#print axioms preserved_op107

theorem preserved_op108 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op108 (Types base) (selected base ops terminal) =
      @ExternalFuns.op108 (Types base) ops := rfl
#print axioms preserved_op108

theorem preserved_op109 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op109 (Types base) (selected base ops terminal) =
      @ExternalFuns.op109 (Types base) ops := rfl
#print axioms preserved_op109

theorem preserved_op110 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op110 (Types base) (selected base ops terminal) =
      @ExternalFuns.op110 (Types base) ops := rfl
#print axioms preserved_op110

theorem preserved_op111 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op111 (Types base) (selected base ops terminal) =
      @ExternalFuns.op111 (Types base) ops := rfl
#print axioms preserved_op111

theorem preserved_op112 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op112 (Types base) (selected base ops terminal) =
      @ExternalFuns.op112 (Types base) ops := rfl
#print axioms preserved_op112

theorem preserved_op113 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op113 (Types base) (selected base ops terminal) =
      @ExternalFuns.op113 (Types base) ops := rfl
#print axioms preserved_op113

theorem preserved_op114 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op114 (Types base) (selected base ops terminal) =
      @ExternalFuns.op114 (Types base) ops := rfl
#print axioms preserved_op114

theorem preserved_op115 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op115 (Types base) (selected base ops terminal) =
      @ExternalFuns.op115 (Types base) ops := rfl
#print axioms preserved_op115

theorem preserved_op116 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op116 (Types base) (selected base ops terminal) =
      @ExternalFuns.op116 (Types base) ops := rfl
#print axioms preserved_op116

theorem preserved_op117 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op117 (Types base) (selected base ops terminal) =
      @ExternalFuns.op117 (Types base) ops := rfl
#print axioms preserved_op117

theorem preserved_op118 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op118 (Types base) (selected base ops terminal) =
      @ExternalFuns.op118 (Types base) ops := rfl
#print axioms preserved_op118

theorem preserved_op119 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op119 (Types base) (selected base ops terminal) =
      @ExternalFuns.op119 (Types base) ops := rfl
#print axioms preserved_op119

theorem preserved_op120 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op120 (Types base) (selected base ops terminal) =
      @ExternalFuns.op120 (Types base) ops := rfl
#print axioms preserved_op120

theorem preserved_op121 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op121 (Types base) (selected base ops terminal) =
      @ExternalFuns.op121 (Types base) ops := rfl
#print axioms preserved_op121

theorem preserved_op122 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op122 (Types base) (selected base ops terminal) =
      @ExternalFuns.op122 (Types base) ops := rfl
#print axioms preserved_op122

theorem preserved_op123 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op123 (Types base) (selected base ops terminal) =
      @ExternalFuns.op123 (Types base) ops := rfl
#print axioms preserved_op123

theorem preserved_op124 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op124 (Types base) (selected base ops terminal) =
      @ExternalFuns.op124 (Types base) ops := rfl
#print axioms preserved_op124

theorem preserved_op125 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op125 (Types base) (selected base ops terminal) =
      @ExternalFuns.op125 (Types base) ops := rfl
#print axioms preserved_op125

theorem preserved_op126 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op126 (Types base) (selected base ops terminal) =
      @ExternalFuns.op126 (Types base) ops := rfl
#print axioms preserved_op126

theorem preserved_op127 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op127 (Types base) (selected base ops terminal) =
      @ExternalFuns.op127 (Types base) ops := rfl
#print axioms preserved_op127

theorem preserved_op128 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op128 (Types base) (selected base ops terminal) =
      @ExternalFuns.op128 (Types base) ops := rfl
#print axioms preserved_op128

theorem preserved_op129 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op129 (Types base) (selected base ops terminal) =
      @ExternalFuns.op129 (Types base) ops := rfl
#print axioms preserved_op129

theorem preserved_op130 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op130 (Types base) (selected base ops terminal) =
      @ExternalFuns.op130 (Types base) ops := rfl
#print axioms preserved_op130

theorem preserved_op131 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op131 (Types base) (selected base ops terminal) =
      @ExternalFuns.op131 (Types base) ops := rfl
#print axioms preserved_op131

theorem preserved_op132 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op132 (Types base) (selected base ops terminal) =
      @ExternalFuns.op132 (Types base) ops := rfl
#print axioms preserved_op132

theorem preserved_op133 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op133 (Types base) (selected base ops terminal) =
      @ExternalFuns.op133 (Types base) ops := rfl
#print axioms preserved_op133

theorem preserved_op134 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op134 (Types base) (selected base ops terminal) =
      @ExternalFuns.op134 (Types base) ops := rfl
#print axioms preserved_op134

theorem preserved_op135 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op135 (Types base) (selected base ops terminal) =
      @ExternalFuns.op135 (Types base) ops := rfl
#print axioms preserved_op135

theorem preserved_op136 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op136 (Types base) (selected base ops terminal) =
      @ExternalFuns.op136 (Types base) ops := rfl
#print axioms preserved_op136

theorem preserved_op137 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op137 (Types base) (selected base ops terminal) =
      @ExternalFuns.op137 (Types base) ops := rfl
#print axioms preserved_op137

theorem preserved_op138 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op138 (Types base) (selected base ops terminal) =
      @ExternalFuns.op138 (Types base) ops := rfl
#print axioms preserved_op138

theorem preserved_op139 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op139 (Types base) (selected base ops terminal) =
      @ExternalFuns.op139 (Types base) ops := rfl
#print axioms preserved_op139

theorem preserved_op140 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op140 (Types base) (selected base ops terminal) =
      @ExternalFuns.op140 (Types base) ops := rfl
#print axioms preserved_op140

theorem preserved_op141 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op141 (Types base) (selected base ops terminal) =
      @ExternalFuns.op141 (Types base) ops := rfl
#print axioms preserved_op141

theorem preserved_op142 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op142 (Types base) (selected base ops terminal) =
      @ExternalFuns.op142 (Types base) ops := rfl
#print axioms preserved_op142

theorem preserved_op143 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op143 (Types base) (selected base ops terminal) =
      @ExternalFuns.op143 (Types base) ops := rfl
#print axioms preserved_op143

theorem preserved_op144 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op144 (Types base) (selected base ops terminal) =
      @ExternalFuns.op144 (Types base) ops := rfl
#print axioms preserved_op144

theorem preserved_op145 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op145 (Types base) (selected base ops terminal) =
      @ExternalFuns.op145 (Types base) ops := rfl
#print axioms preserved_op145

theorem preserved_op146 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op146 (Types base) (selected base ops terminal) =
      @ExternalFuns.op146 (Types base) ops := rfl
#print axioms preserved_op146

theorem preserved_op147 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op147 (Types base) (selected base ops terminal) =
      @ExternalFuns.op147 (Types base) ops := rfl
#print axioms preserved_op147

theorem preserved_op148 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op148 (Types base) (selected base ops terminal) =
      @ExternalFuns.op148 (Types base) ops := rfl
#print axioms preserved_op148

theorem preserved_op149 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op149 (Types base) (selected base ops terminal) =
      @ExternalFuns.op149 (Types base) ops := rfl
#print axioms preserved_op149

theorem preserved_op150 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op150 (Types base) (selected base ops terminal) =
      @ExternalFuns.op150 (Types base) ops := rfl
#print axioms preserved_op150

theorem preserved_op151 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op151 (Types base) (selected base ops terminal) =
      @ExternalFuns.op151 (Types base) ops := rfl
#print axioms preserved_op151

theorem preserved_op152 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op152 (Types base) (selected base ops terminal) =
      @ExternalFuns.op152 (Types base) ops := rfl
#print axioms preserved_op152

theorem preserved_op153 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op153 (Types base) (selected base ops terminal) =
      @ExternalFuns.op153 (Types base) ops := rfl
#print axioms preserved_op153

theorem preserved_op154 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op154 (Types base) (selected base ops terminal) =
      @ExternalFuns.op154 (Types base) ops := rfl
#print axioms preserved_op154

theorem preserved_op155 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op155 (Types base) (selected base ops terminal) =
      @ExternalFuns.op155 (Types base) ops := rfl
#print axioms preserved_op155

theorem preserved_op156 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op156 (Types base) (selected base ops terminal) =
      @ExternalFuns.op156 (Types base) ops := rfl
#print axioms preserved_op156

theorem preserved_op157 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op157 (Types base) (selected base ops terminal) =
      @ExternalFuns.op157 (Types base) ops := rfl
#print axioms preserved_op157

theorem preserved_op158 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op158 (Types base) (selected base ops terminal) =
      @ExternalFuns.op158 (Types base) ops := rfl
#print axioms preserved_op158

theorem preserved_op159 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op159 (Types base) (selected base ops terminal) =
      @ExternalFuns.op159 (Types base) ops := rfl
#print axioms preserved_op159

theorem preserved_op160 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op160 (Types base) (selected base ops terminal) =
      @ExternalFuns.op160 (Types base) ops := rfl
#print axioms preserved_op160

theorem preserved_op161 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op161 (Types base) (selected base ops terminal) =
      @ExternalFuns.op161 (Types base) ops := rfl
#print axioms preserved_op161

theorem preserved_op162 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op162 (Types base) (selected base ops terminal) =
      @ExternalFuns.op162 (Types base) ops := rfl
#print axioms preserved_op162

theorem preserved_op163 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op163 (Types base) (selected base ops terminal) =
      @ExternalFuns.op163 (Types base) ops := rfl
#print axioms preserved_op163

theorem preserved_op164 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op164 (Types base) (selected base ops terminal) =
      @ExternalFuns.op164 (Types base) ops := rfl
#print axioms preserved_op164

theorem preserved_op165 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op165 (Types base) (selected base ops terminal) =
      @ExternalFuns.op165 (Types base) ops := rfl
#print axioms preserved_op165

theorem preserved_op166 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op166 (Types base) (selected base ops terminal) =
      @ExternalFuns.op166 (Types base) ops := rfl
#print axioms preserved_op166

theorem preserved_op167 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op167 (Types base) (selected base ops terminal) =
      @ExternalFuns.op167 (Types base) ops := rfl
#print axioms preserved_op167

theorem preserved_op168 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op168 (Types base) (selected base ops terminal) =
      @ExternalFuns.op168 (Types base) ops := rfl
#print axioms preserved_op168

theorem preserved_op169 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op169 (Types base) (selected base ops terminal) =
      @ExternalFuns.op169 (Types base) ops := rfl
#print axioms preserved_op169

theorem preserved_op170 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op170 (Types base) (selected base ops terminal) =
      @ExternalFuns.op170 (Types base) ops := rfl
#print axioms preserved_op170

theorem preserved_op171 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op171 (Types base) (selected base ops terminal) =
      @ExternalFuns.op171 (Types base) ops := rfl
#print axioms preserved_op171

theorem preserved_op172 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op172 (Types base) (selected base ops terminal) =
      @ExternalFuns.op172 (Types base) ops := rfl
#print axioms preserved_op172

theorem preserved_op173 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op173 (Types base) (selected base ops terminal) =
      @ExternalFuns.op173 (Types base) ops := rfl
#print axioms preserved_op173

theorem preserved_op174 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op174 (Types base) (selected base ops terminal) =
      @ExternalFuns.op174 (Types base) ops := rfl
#print axioms preserved_op174

theorem preserved_op175 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op175 (Types base) (selected base ops terminal) =
      @ExternalFuns.op175 (Types base) ops := rfl
#print axioms preserved_op175

theorem preserved_op176 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op176 (Types base) (selected base ops terminal) =
      @ExternalFuns.op176 (Types base) ops := rfl
#print axioms preserved_op176

theorem preserved_op177 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op177 (Types base) (selected base ops terminal) =
      @ExternalFuns.op177 (Types base) ops := rfl
#print axioms preserved_op177

theorem preserved_op178 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op178 (Types base) (selected base ops terminal) =
      @ExternalFuns.op178 (Types base) ops := rfl
#print axioms preserved_op178

theorem preserved_op179 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op179 (Types base) (selected base ops terminal) =
      @ExternalFuns.op179 (Types base) ops := rfl
#print axioms preserved_op179

theorem preserved_op180 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op180 (Types base) (selected base ops terminal) =
      @ExternalFuns.op180 (Types base) ops := rfl
#print axioms preserved_op180

theorem preserved_op181 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op181 (Types base) (selected base ops terminal) =
      @ExternalFuns.op181 (Types base) ops := rfl
#print axioms preserved_op181

theorem preserved_op182 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op182 (Types base) (selected base ops terminal) =
      @ExternalFuns.op182 (Types base) ops := rfl
#print axioms preserved_op182

theorem preserved_op183 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op183 (Types base) (selected base ops terminal) =
      @ExternalFuns.op183 (Types base) ops := rfl
#print axioms preserved_op183

theorem preserved_op184 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op184 (Types base) (selected base ops terminal) =
      @ExternalFuns.op184 (Types base) ops := rfl
#print axioms preserved_op184

theorem preserved_op185 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op185 (Types base) (selected base ops terminal) =
      @ExternalFuns.op185 (Types base) ops := rfl
#print axioms preserved_op185

theorem preserved_op186 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op186 (Types base) (selected base ops terminal) =
      @ExternalFuns.op186 (Types base) ops := rfl
#print axioms preserved_op186

theorem preserved_op187 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op187 (Types base) (selected base ops terminal) =
      @ExternalFuns.op187 (Types base) ops := rfl
#print axioms preserved_op187

theorem preserved_op188 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op188 (Types base) (selected base ops terminal) =
      @ExternalFuns.op188 (Types base) ops := rfl
#print axioms preserved_op188

theorem preserved_op189 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op189 (Types base) (selected base ops terminal) =
      @ExternalFuns.op189 (Types base) ops := rfl
#print axioms preserved_op189

theorem preserved_op190 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op190 (Types base) (selected base ops terminal) =
      @ExternalFuns.op190 (Types base) ops := rfl
#print axioms preserved_op190

theorem preserved_op191 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op191 (Types base) (selected base ops terminal) =
      @ExternalFuns.op191 (Types base) ops := rfl
#print axioms preserved_op191

theorem preserved_op192 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op192 (Types base) (selected base ops terminal) =
      @ExternalFuns.op192 (Types base) ops := rfl
#print axioms preserved_op192

theorem preserved_op193 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op193 (Types base) (selected base ops terminal) =
      @ExternalFuns.op193 (Types base) ops := rfl
#print axioms preserved_op193

theorem preserved_op194 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op194 (Types base) (selected base ops terminal) =
      @ExternalFuns.op194 (Types base) ops := rfl
#print axioms preserved_op194

theorem preserved_op195 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op195 (Types base) (selected base ops terminal) =
      @ExternalFuns.op195 (Types base) ops := rfl
#print axioms preserved_op195

theorem preserved_op196 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op196 (Types base) (selected base ops terminal) =
      @ExternalFuns.op196 (Types base) ops := rfl
#print axioms preserved_op196

theorem preserved_op197 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op197 (Types base) (selected base ops terminal) =
      @ExternalFuns.op197 (Types base) ops := rfl
#print axioms preserved_op197

theorem preserved_op198 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op198 (Types base) (selected base ops terminal) =
      @ExternalFuns.op198 (Types base) ops := rfl
#print axioms preserved_op198

theorem preserved_op199 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op199 (Types base) (selected base ops terminal) =
      @ExternalFuns.op199 (Types base) ops := rfl
#print axioms preserved_op199

theorem preserved_op200 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op200 (Types base) (selected base ops terminal) =
      @ExternalFuns.op200 (Types base) ops := rfl
#print axioms preserved_op200

theorem preserved_op201 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op201 (Types base) (selected base ops terminal) =
      @ExternalFuns.op201 (Types base) ops := rfl
#print axioms preserved_op201

theorem preserved_op202 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op202 (Types base) (selected base ops terminal) =
      @ExternalFuns.op202 (Types base) ops := rfl
#print axioms preserved_op202

theorem preserved_op203 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op203 (Types base) (selected base ops terminal) =
      @ExternalFuns.op203 (Types base) ops := rfl
#print axioms preserved_op203

theorem preserved_op204 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op204 (Types base) (selected base ops terminal) =
      @ExternalFuns.op204 (Types base) ops := rfl
#print axioms preserved_op204

theorem preserved_op205 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op205 (Types base) (selected base ops terminal) =
      @ExternalFuns.op205 (Types base) ops := rfl
#print axioms preserved_op205

theorem preserved_op206 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op206 (Types base) (selected base ops terminal) =
      @ExternalFuns.op206 (Types base) ops := rfl
#print axioms preserved_op206

theorem preserved_op207 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op207 (Types base) (selected base ops terminal) =
      @ExternalFuns.op207 (Types base) ops := rfl
#print axioms preserved_op207

theorem preserved_op208 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op208 (Types base) (selected base ops terminal) =
      @ExternalFuns.op208 (Types base) ops := rfl
#print axioms preserved_op208

theorem preserved_op209 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op209 (Types base) (selected base ops terminal) =
      @ExternalFuns.op209 (Types base) ops := rfl
#print axioms preserved_op209

theorem preserved_op210 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op210 (Types base) (selected base ops terminal) =
      @ExternalFuns.op210 (Types base) ops := rfl
#print axioms preserved_op210

theorem preserved_op211 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op211 (Types base) (selected base ops terminal) =
      @ExternalFuns.op211 (Types base) ops := rfl
#print axioms preserved_op211

theorem preserved_op212 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op212 (Types base) (selected base ops terminal) =
      @ExternalFuns.op212 (Types base) ops := rfl
#print axioms preserved_op212

theorem preserved_op213 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op213 (Types base) (selected base ops terminal) =
      @ExternalFuns.op213 (Types base) ops := rfl
#print axioms preserved_op213

theorem preserved_op214 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op214 (Types base) (selected base ops terminal) =
      @ExternalFuns.op214 (Types base) ops := rfl
#print axioms preserved_op214

theorem preserved_op215 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op215 (Types base) (selected base ops terminal) =
      @ExternalFuns.op215 (Types base) ops := rfl
#print axioms preserved_op215

theorem preserved_op216 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op216 (Types base) (selected base ops terminal) =
      @ExternalFuns.op216 (Types base) ops := rfl
#print axioms preserved_op216

theorem preserved_op217 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op217 (Types base) (selected base ops terminal) =
      @ExternalFuns.op217 (Types base) ops := rfl
#print axioms preserved_op217

theorem preserved_op218 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op218 (Types base) (selected base ops terminal) =
      @ExternalFuns.op218 (Types base) ops := rfl
#print axioms preserved_op218

theorem preserved_op219 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op219 (Types base) (selected base ops terminal) =
      @ExternalFuns.op219 (Types base) ops := rfl
#print axioms preserved_op219

theorem preserved_op220 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op220 (Types base) (selected base ops terminal) =
      @ExternalFuns.op220 (Types base) ops := rfl
#print axioms preserved_op220

theorem preserved_op221 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op221 (Types base) (selected base ops terminal) =
      @ExternalFuns.op221 (Types base) ops := rfl
#print axioms preserved_op221

theorem preserved_op222 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op222 (Types base) (selected base ops terminal) =
      @ExternalFuns.op222 (Types base) ops := rfl
#print axioms preserved_op222

theorem preserved_op223 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op223 (Types base) (selected base ops terminal) =
      @ExternalFuns.op223 (Types base) ops := rfl
#print axioms preserved_op223

theorem preserved_op224 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op224 (Types base) (selected base ops terminal) =
      @ExternalFuns.op224 (Types base) ops := rfl
#print axioms preserved_op224

theorem preserved_op225 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op225 (Types base) (selected base ops terminal) =
      @ExternalFuns.op225 (Types base) ops := rfl
#print axioms preserved_op225

theorem preserved_op226 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op226 (Types base) (selected base ops terminal) =
      @ExternalFuns.op226 (Types base) ops := rfl
#print axioms preserved_op226

theorem preserved_op228 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op228 (Types base) (selected base ops terminal) =
      @ExternalFuns.op228 (Types base) ops := rfl
#print axioms preserved_op228

theorem preserved_op229 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op229 (Types base) (selected base ops terminal) =
      @ExternalFuns.op229 (Types base) ops := rfl
#print axioms preserved_op229

theorem preserved_op230 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op230 (Types base) (selected base ops terminal) =
      @ExternalFuns.op230 (Types base) ops := rfl
#print axioms preserved_op230

theorem preserved_op231 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op231 (Types base) (selected base ops terminal) =
      @ExternalFuns.op231 (Types base) ops := rfl
#print axioms preserved_op231

theorem preserved_op232 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op232 (Types base) (selected base ops terminal) =
      @ExternalFuns.op232 (Types base) ops := rfl
#print axioms preserved_op232

theorem preserved_op233 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op233 (Types base) (selected base ops terminal) =
      @ExternalFuns.op233 (Types base) ops := rfl
#print axioms preserved_op233

theorem preserved_op234 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op234 (Types base) (selected base ops terminal) =
      @ExternalFuns.op234 (Types base) ops := rfl
#print axioms preserved_op234

theorem preserved_op235 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op235 (Types base) (selected base ops terminal) =
      @ExternalFuns.op235 (Types base) ops := rfl
#print axioms preserved_op235

theorem preserved_op236 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op236 (Types base) (selected base ops terminal) =
      @ExternalFuns.op236 (Types base) ops := rfl
#print axioms preserved_op236

theorem preserved_op237 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op237 (Types base) (selected base ops terminal) =
      @ExternalFuns.op237 (Types base) ops := rfl
#print axioms preserved_op237

theorem preserved_op238 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op238 (Types base) (selected base ops terminal) =
      @ExternalFuns.op238 (Types base) ops := rfl
#print axioms preserved_op238

theorem preserved_op239 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op239 (Types base) (selected base ops terminal) =
      @ExternalFuns.op239 (Types base) ops := rfl
#print axioms preserved_op239

theorem preserved_op240 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op240 (Types base) (selected base ops terminal) =
      @ExternalFuns.op240 (Types base) ops := rfl
#print axioms preserved_op240

theorem preserved_op241 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op241 (Types base) (selected base ops terminal) =
      @ExternalFuns.op241 (Types base) ops := rfl
#print axioms preserved_op241

theorem preserved_op242 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op242 (Types base) (selected base ops terminal) =
      @ExternalFuns.op242 (Types base) ops := rfl
#print axioms preserved_op242

theorem preserved_op243 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op243 (Types base) (selected base ops terminal) =
      @ExternalFuns.op243 (Types base) ops := rfl
#print axioms preserved_op243

theorem preserved_op244 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op244 (Types base) (selected base ops terminal) =
      @ExternalFuns.op244 (Types base) ops := rfl
#print axioms preserved_op244

theorem preserved_op245 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op245 (Types base) (selected base ops terminal) =
      @ExternalFuns.op245 (Types base) ops := rfl
#print axioms preserved_op245

theorem preserved_op246 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op246 (Types base) (selected base ops terminal) =
      @ExternalFuns.op246 (Types base) ops := rfl
#print axioms preserved_op246

theorem preserved_op247 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op247 (Types base) (selected base ops terminal) =
      @ExternalFuns.op247 (Types base) ops := rfl
#print axioms preserved_op247

theorem preserved_op248 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op248 (Types base) (selected base ops terminal) =
      @ExternalFuns.op248 (Types base) ops := rfl
#print axioms preserved_op248

theorem preserved_op249 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op249 (Types base) (selected base ops terminal) =
      @ExternalFuns.op249 (Types base) ops := rfl
#print axioms preserved_op249

theorem preserved_op250 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op250 (Types base) (selected base ops terminal) =
      @ExternalFuns.op250 (Types base) ops := rfl
#print axioms preserved_op250

theorem preserved_op251 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op251 (Types base) (selected base ops terminal) =
      @ExternalFuns.op251 (Types base) ops := rfl
#print axioms preserved_op251

theorem preserved_op252 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op252 (Types base) (selected base ops terminal) =
      @ExternalFuns.op252 (Types base) ops := rfl
#print axioms preserved_op252

theorem preserved_op253 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op253 (Types base) (selected base ops terminal) =
      @ExternalFuns.op253 (Types base) ops := rfl
#print axioms preserved_op253

theorem preserved_op254 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op254 (Types base) (selected base ops terminal) =
      @ExternalFuns.op254 (Types base) ops := rfl
#print axioms preserved_op254

theorem preserved_op255 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op255 (Types base) (selected base ops terminal) =
      @ExternalFuns.op255 (Types base) ops := rfl
#print axioms preserved_op255

theorem preserved_op256 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op256 (Types base) (selected base ops terminal) =
      @ExternalFuns.op256 (Types base) ops := rfl
#print axioms preserved_op256

theorem preserved_op257 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op257 (Types base) (selected base ops terminal) =
      @ExternalFuns.op257 (Types base) ops := rfl
#print axioms preserved_op257

theorem preserved_op258 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op258 (Types base) (selected base ops terminal) =
      @ExternalFuns.op258 (Types base) ops := rfl
#print axioms preserved_op258

theorem preserved_op259 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op259 (Types base) (selected base ops terminal) =
      @ExternalFuns.op259 (Types base) ops := rfl
#print axioms preserved_op259

theorem preserved_op260 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op260 (Types base) (selected base ops terminal) =
      @ExternalFuns.op260 (Types base) ops := rfl
#print axioms preserved_op260

theorem preserved_op261 (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (terminal : Terminal) :
    @ExternalFuns.op261 (Types base) (selected base ops terminal) =
      @ExternalFuns.op261 (Types base) ops := rfl
#print axioms preserved_op261

end PV_B3P_Install227
