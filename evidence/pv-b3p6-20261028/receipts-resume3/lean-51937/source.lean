import PV_B3P_MaskOrdered132
import R1Z.ProverRwFullExternalFuns
namespace PV_B3P_Install132
open Aeneas Aeneas.Std PV_B3P_132 ProverRwFull
set_option autoImplicit false
noncomputable section

def raw : Array reference132.Cell 3803#usize := Classical.choose PV_B3P_MaskOrdered132.complete_result

theorem raw_law : reference132.cells = .ok (raw,3803#usize) ∧
    raw.val.map PV_B3P_MaskPrefix132.decode = PV_B3P_MaskModel132.cells :=
  Classical.choose_spec PV_B3P_MaskOrdered132.complete_result

def convert (x : reference132.Cell) : aspis_statement.trace_v4.TraceCell := ⟨x.row,x.column⟩
def value : alloc.vec.Vec aspis_statement.trace_v4.TraceCell :=
  ⟨raw.val.map convert,by have h := raw.property; simp only [List.length_map]; scalar_tac⟩

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns base) : @ExternalFuns base :=
  letI := base
  {ops with op132 := .ok (.Ok value)}

theorem source (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op132 base (selected base ops) = .ok (.Ok value) := rfl

theorem reference (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op132 base (selected base ops) = (do
      let (out,_) ← reference132.cells
      let v : alloc.vec.Vec aspis_statement.trace_v4.TraceCell :=
        ⟨out.val.map convert,by have h := out.property; simp only [List.length_map]; scalar_tac⟩
      .ok (.Ok v)) := by
  rw [raw_law.1]
  rfl

theorem value_law : value.val.map (fun x => (x.row.val,x.column.val)) = PV_B3P_MaskModel132.cells := by
  simpa only [value,List.map_map,Function.comp_def,convert,PV_B3P_MaskPrefix132.decode] using raw_law.2

theorem count_law : value.val.length = 3803 := by
  simp only [value,List.length_map]
  exact raw.property

theorem nonvacuity (base : ExternalTypes) (ops : @ExternalFuns base) :
    ∃ v, @ExternalFuns.op132 base (selected base ops) = .ok (.Ok v) := ⟨value,rfl⟩

#print axioms raw_law
#print axioms source
#print axioms reference
#print axioms value_law
#print axioms count_law
#print axioms nonvacuity
theorem preserved_op0 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op0 base (selected base ops) = @ExternalFuns.op0 base ops := rfl
#print axioms preserved_op0
theorem preserved_op1 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op1 base (selected base ops) = @ExternalFuns.op1 base ops := rfl
#print axioms preserved_op1
theorem preserved_op2 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op2 base (selected base ops) = @ExternalFuns.op2 base ops := rfl
#print axioms preserved_op2
theorem preserved_op3 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op3 base (selected base ops) = @ExternalFuns.op3 base ops := rfl
#print axioms preserved_op3
theorem preserved_op4 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op4 base (selected base ops) = @ExternalFuns.op4 base ops := rfl
#print axioms preserved_op4
theorem preserved_op5 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op5 base (selected base ops) = @ExternalFuns.op5 base ops := rfl
#print axioms preserved_op5
theorem preserved_op6 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op6 base (selected base ops) = @ExternalFuns.op6 base ops := rfl
#print axioms preserved_op6
theorem preserved_op7 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op7 base (selected base ops) = @ExternalFuns.op7 base ops := rfl
#print axioms preserved_op7
theorem preserved_op8 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op8 base (selected base ops) = @ExternalFuns.op8 base ops := rfl
#print axioms preserved_op8
theorem preserved_op9 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op9 base (selected base ops) = @ExternalFuns.op9 base ops := rfl
#print axioms preserved_op9
theorem preserved_op10 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op10 base (selected base ops) = @ExternalFuns.op10 base ops := rfl
#print axioms preserved_op10
theorem preserved_op11 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op11 base (selected base ops) = @ExternalFuns.op11 base ops := rfl
#print axioms preserved_op11
theorem preserved_op12 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op12 base (selected base ops) = @ExternalFuns.op12 base ops := rfl
#print axioms preserved_op12
theorem preserved_op13 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op13 base (selected base ops) = @ExternalFuns.op13 base ops := rfl
#print axioms preserved_op13
theorem preserved_op14 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op14 base (selected base ops) = @ExternalFuns.op14 base ops := rfl
#print axioms preserved_op14
theorem preserved_op15 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op15 base (selected base ops) = @ExternalFuns.op15 base ops := rfl
#print axioms preserved_op15
theorem preserved_op16 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op16 base (selected base ops) = @ExternalFuns.op16 base ops := rfl
#print axioms preserved_op16
theorem preserved_op17 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op17 base (selected base ops) = @ExternalFuns.op17 base ops := rfl
#print axioms preserved_op17
theorem preserved_op18 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op18 base (selected base ops) = @ExternalFuns.op18 base ops := rfl
#print axioms preserved_op18
theorem preserved_op19 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op19 base (selected base ops) = @ExternalFuns.op19 base ops := rfl
#print axioms preserved_op19
theorem preserved_op20 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op20 base (selected base ops) = @ExternalFuns.op20 base ops := rfl
#print axioms preserved_op20
theorem preserved_op21 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op21 base (selected base ops) = @ExternalFuns.op21 base ops := rfl
#print axioms preserved_op21
theorem preserved_op22 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op22 base (selected base ops) = @ExternalFuns.op22 base ops := rfl
#print axioms preserved_op22
theorem preserved_op23 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op23 base (selected base ops) = @ExternalFuns.op23 base ops := rfl
#print axioms preserved_op23
theorem preserved_op24 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op24 base (selected base ops) = @ExternalFuns.op24 base ops := rfl
#print axioms preserved_op24
theorem preserved_op25 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op25 base (selected base ops) = @ExternalFuns.op25 base ops := rfl
#print axioms preserved_op25
theorem preserved_op26 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op26 base (selected base ops) = @ExternalFuns.op26 base ops := rfl
#print axioms preserved_op26
theorem preserved_op27 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op27 base (selected base ops) = @ExternalFuns.op27 base ops := rfl
#print axioms preserved_op27
theorem preserved_op28 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op28 base (selected base ops) = @ExternalFuns.op28 base ops := rfl
#print axioms preserved_op28
theorem preserved_op29 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op29 base (selected base ops) = @ExternalFuns.op29 base ops := rfl
#print axioms preserved_op29
theorem preserved_op30 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op30 base (selected base ops) = @ExternalFuns.op30 base ops := rfl
#print axioms preserved_op30
theorem preserved_op31 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op31 base (selected base ops) = @ExternalFuns.op31 base ops := rfl
#print axioms preserved_op31
theorem preserved_op32 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op32 base (selected base ops) = @ExternalFuns.op32 base ops := rfl
#print axioms preserved_op32
theorem preserved_op33 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op33 base (selected base ops) = @ExternalFuns.op33 base ops := rfl
#print axioms preserved_op33
theorem preserved_op34 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op34 base (selected base ops) = @ExternalFuns.op34 base ops := rfl
#print axioms preserved_op34
theorem preserved_op35 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op35 base (selected base ops) = @ExternalFuns.op35 base ops := rfl
#print axioms preserved_op35
theorem preserved_op36 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op36 base (selected base ops) = @ExternalFuns.op36 base ops := rfl
#print axioms preserved_op36
theorem preserved_op37 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op37 base (selected base ops) = @ExternalFuns.op37 base ops := rfl
#print axioms preserved_op37
theorem preserved_op38 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op38 base (selected base ops) = @ExternalFuns.op38 base ops := rfl
#print axioms preserved_op38
theorem preserved_op39 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op39 base (selected base ops) = @ExternalFuns.op39 base ops := rfl
#print axioms preserved_op39
theorem preserved_op40 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op40 base (selected base ops) = @ExternalFuns.op40 base ops := rfl
#print axioms preserved_op40
theorem preserved_op41 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op41 base (selected base ops) = @ExternalFuns.op41 base ops := rfl
#print axioms preserved_op41
theorem preserved_op42 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op42 base (selected base ops) = @ExternalFuns.op42 base ops := rfl
#print axioms preserved_op42
theorem preserved_op43 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op43 base (selected base ops) = @ExternalFuns.op43 base ops := rfl
#print axioms preserved_op43
theorem preserved_op44 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op44 base (selected base ops) = @ExternalFuns.op44 base ops := rfl
#print axioms preserved_op44
theorem preserved_op45 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op45 base (selected base ops) = @ExternalFuns.op45 base ops := rfl
#print axioms preserved_op45
theorem preserved_op46 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op46 base (selected base ops) = @ExternalFuns.op46 base ops := rfl
#print axioms preserved_op46
theorem preserved_op47 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op47 base (selected base ops) = @ExternalFuns.op47 base ops := rfl
#print axioms preserved_op47
theorem preserved_op48 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op48 base (selected base ops) = @ExternalFuns.op48 base ops := rfl
#print axioms preserved_op48
theorem preserved_op49 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op49 base (selected base ops) = @ExternalFuns.op49 base ops := rfl
#print axioms preserved_op49
theorem preserved_op50 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op50 base (selected base ops) = @ExternalFuns.op50 base ops := rfl
#print axioms preserved_op50
theorem preserved_op51 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op51 base (selected base ops) = @ExternalFuns.op51 base ops := rfl
#print axioms preserved_op51
theorem preserved_op52 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op52 base (selected base ops) = @ExternalFuns.op52 base ops := rfl
#print axioms preserved_op52
theorem preserved_op53 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op53 base (selected base ops) = @ExternalFuns.op53 base ops := rfl
#print axioms preserved_op53
theorem preserved_op54 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op54 base (selected base ops) = @ExternalFuns.op54 base ops := rfl
#print axioms preserved_op54
theorem preserved_op55 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op55 base (selected base ops) = @ExternalFuns.op55 base ops := rfl
#print axioms preserved_op55
theorem preserved_op56 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op56 base (selected base ops) = @ExternalFuns.op56 base ops := rfl
#print axioms preserved_op56
theorem preserved_op57 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op57 base (selected base ops) = @ExternalFuns.op57 base ops := rfl
#print axioms preserved_op57
theorem preserved_op58 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op58 base (selected base ops) = @ExternalFuns.op58 base ops := rfl
#print axioms preserved_op58
theorem preserved_op59 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op59 base (selected base ops) = @ExternalFuns.op59 base ops := rfl
#print axioms preserved_op59
theorem preserved_op60 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op60 base (selected base ops) = @ExternalFuns.op60 base ops := rfl
#print axioms preserved_op60
theorem preserved_op61 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op61 base (selected base ops) = @ExternalFuns.op61 base ops := rfl
#print axioms preserved_op61
theorem preserved_op62 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op62 base (selected base ops) = @ExternalFuns.op62 base ops := rfl
#print axioms preserved_op62
theorem preserved_op63 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op63 base (selected base ops) = @ExternalFuns.op63 base ops := rfl
#print axioms preserved_op63
theorem preserved_op64 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op64 base (selected base ops) = @ExternalFuns.op64 base ops := rfl
#print axioms preserved_op64
theorem preserved_op65 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op65 base (selected base ops) = @ExternalFuns.op65 base ops := rfl
#print axioms preserved_op65
theorem preserved_op66 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op66 base (selected base ops) = @ExternalFuns.op66 base ops := rfl
#print axioms preserved_op66
theorem preserved_op67 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op67 base (selected base ops) = @ExternalFuns.op67 base ops := rfl
#print axioms preserved_op67
theorem preserved_op68 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op68 base (selected base ops) = @ExternalFuns.op68 base ops := rfl
#print axioms preserved_op68
theorem preserved_op69 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op69 base (selected base ops) = @ExternalFuns.op69 base ops := rfl
#print axioms preserved_op69
theorem preserved_op70 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op70 base (selected base ops) = @ExternalFuns.op70 base ops := rfl
#print axioms preserved_op70
theorem preserved_op71 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op71 base (selected base ops) = @ExternalFuns.op71 base ops := rfl
#print axioms preserved_op71
theorem preserved_op72 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op72 base (selected base ops) = @ExternalFuns.op72 base ops := rfl
#print axioms preserved_op72
theorem preserved_op73 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op73 base (selected base ops) = @ExternalFuns.op73 base ops := rfl
#print axioms preserved_op73
theorem preserved_op74 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op74 base (selected base ops) = @ExternalFuns.op74 base ops := rfl
#print axioms preserved_op74
theorem preserved_op75 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op75 base (selected base ops) = @ExternalFuns.op75 base ops := rfl
#print axioms preserved_op75
theorem preserved_op76 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op76 base (selected base ops) = @ExternalFuns.op76 base ops := rfl
#print axioms preserved_op76
theorem preserved_op77 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op77 base (selected base ops) = @ExternalFuns.op77 base ops := rfl
#print axioms preserved_op77
theorem preserved_op78 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op78 base (selected base ops) = @ExternalFuns.op78 base ops := rfl
#print axioms preserved_op78
theorem preserved_op79 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op79 base (selected base ops) = @ExternalFuns.op79 base ops := rfl
#print axioms preserved_op79
theorem preserved_op80 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op80 base (selected base ops) = @ExternalFuns.op80 base ops := rfl
#print axioms preserved_op80
theorem preserved_op81 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op81 base (selected base ops) = @ExternalFuns.op81 base ops := rfl
#print axioms preserved_op81
theorem preserved_op82 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op82 base (selected base ops) = @ExternalFuns.op82 base ops := rfl
#print axioms preserved_op82
theorem preserved_op83 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op83 base (selected base ops) = @ExternalFuns.op83 base ops := rfl
#print axioms preserved_op83
theorem preserved_op84 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op84 base (selected base ops) = @ExternalFuns.op84 base ops := rfl
#print axioms preserved_op84
theorem preserved_op85 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op85 base (selected base ops) = @ExternalFuns.op85 base ops := rfl
#print axioms preserved_op85
theorem preserved_op86 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op86 base (selected base ops) = @ExternalFuns.op86 base ops := rfl
#print axioms preserved_op86
theorem preserved_op87 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op87 base (selected base ops) = @ExternalFuns.op87 base ops := rfl
#print axioms preserved_op87
theorem preserved_op88 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op88 base (selected base ops) = @ExternalFuns.op88 base ops := rfl
#print axioms preserved_op88
theorem preserved_op89 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op89 base (selected base ops) = @ExternalFuns.op89 base ops := rfl
#print axioms preserved_op89
theorem preserved_op90 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op90 base (selected base ops) = @ExternalFuns.op90 base ops := rfl
#print axioms preserved_op90
theorem preserved_op91 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op91 base (selected base ops) = @ExternalFuns.op91 base ops := rfl
#print axioms preserved_op91
theorem preserved_op92 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op92 base (selected base ops) = @ExternalFuns.op92 base ops := rfl
#print axioms preserved_op92
theorem preserved_op93 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op93 base (selected base ops) = @ExternalFuns.op93 base ops := rfl
#print axioms preserved_op93
theorem preserved_op94 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op94 base (selected base ops) = @ExternalFuns.op94 base ops := rfl
#print axioms preserved_op94
theorem preserved_op95 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op95 base (selected base ops) = @ExternalFuns.op95 base ops := rfl
#print axioms preserved_op95
theorem preserved_op96 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op96 base (selected base ops) = @ExternalFuns.op96 base ops := rfl
#print axioms preserved_op96
theorem preserved_op97 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op97 base (selected base ops) = @ExternalFuns.op97 base ops := rfl
#print axioms preserved_op97
theorem preserved_op98 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op98 base (selected base ops) = @ExternalFuns.op98 base ops := rfl
#print axioms preserved_op98
theorem preserved_op99 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op99 base (selected base ops) = @ExternalFuns.op99 base ops := rfl
#print axioms preserved_op99
theorem preserved_op100 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op100 base (selected base ops) = @ExternalFuns.op100 base ops := rfl
#print axioms preserved_op100
theorem preserved_op101 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op101 base (selected base ops) = @ExternalFuns.op101 base ops := rfl
#print axioms preserved_op101
theorem preserved_op102 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op102 base (selected base ops) = @ExternalFuns.op102 base ops := rfl
#print axioms preserved_op102
theorem preserved_op103 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op103 base (selected base ops) = @ExternalFuns.op103 base ops := rfl
#print axioms preserved_op103
theorem preserved_op104 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op104 base (selected base ops) = @ExternalFuns.op104 base ops := rfl
#print axioms preserved_op104
theorem preserved_op105 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op105 base (selected base ops) = @ExternalFuns.op105 base ops := rfl
#print axioms preserved_op105
theorem preserved_op106 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op106 base (selected base ops) = @ExternalFuns.op106 base ops := rfl
#print axioms preserved_op106
theorem preserved_op107 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op107 base (selected base ops) = @ExternalFuns.op107 base ops := rfl
#print axioms preserved_op107
theorem preserved_op108 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op108 base (selected base ops) = @ExternalFuns.op108 base ops := rfl
#print axioms preserved_op108
theorem preserved_op109 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op109 base (selected base ops) = @ExternalFuns.op109 base ops := rfl
#print axioms preserved_op109
theorem preserved_op110 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op110 base (selected base ops) = @ExternalFuns.op110 base ops := rfl
#print axioms preserved_op110
theorem preserved_op111 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op111 base (selected base ops) = @ExternalFuns.op111 base ops := rfl
#print axioms preserved_op111
theorem preserved_op112 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op112 base (selected base ops) = @ExternalFuns.op112 base ops := rfl
#print axioms preserved_op112
theorem preserved_op113 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op113 base (selected base ops) = @ExternalFuns.op113 base ops := rfl
#print axioms preserved_op113
theorem preserved_op114 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op114 base (selected base ops) = @ExternalFuns.op114 base ops := rfl
#print axioms preserved_op114
theorem preserved_op115 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op115 base (selected base ops) = @ExternalFuns.op115 base ops := rfl
#print axioms preserved_op115
theorem preserved_op116 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op116 base (selected base ops) = @ExternalFuns.op116 base ops := rfl
#print axioms preserved_op116
theorem preserved_op117 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op117 base (selected base ops) = @ExternalFuns.op117 base ops := rfl
#print axioms preserved_op117
theorem preserved_op118 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op118 base (selected base ops) = @ExternalFuns.op118 base ops := rfl
#print axioms preserved_op118
theorem preserved_op119 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op119 base (selected base ops) = @ExternalFuns.op119 base ops := rfl
#print axioms preserved_op119
theorem preserved_op120 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op120 base (selected base ops) = @ExternalFuns.op120 base ops := rfl
#print axioms preserved_op120
theorem preserved_op121 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op121 base (selected base ops) = @ExternalFuns.op121 base ops := rfl
#print axioms preserved_op121
theorem preserved_op122 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op122 base (selected base ops) = @ExternalFuns.op122 base ops := rfl
#print axioms preserved_op122
theorem preserved_op123 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op123 base (selected base ops) = @ExternalFuns.op123 base ops := rfl
#print axioms preserved_op123
theorem preserved_op124 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op124 base (selected base ops) = @ExternalFuns.op124 base ops := rfl
#print axioms preserved_op124
theorem preserved_op125 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op125 base (selected base ops) = @ExternalFuns.op125 base ops := rfl
#print axioms preserved_op125
theorem preserved_op126 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op126 base (selected base ops) = @ExternalFuns.op126 base ops := rfl
#print axioms preserved_op126
theorem preserved_op127 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op127 base (selected base ops) = @ExternalFuns.op127 base ops := rfl
#print axioms preserved_op127
theorem preserved_op128 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op128 base (selected base ops) = @ExternalFuns.op128 base ops := rfl
#print axioms preserved_op128
theorem preserved_op129 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op129 base (selected base ops) = @ExternalFuns.op129 base ops := rfl
#print axioms preserved_op129
theorem preserved_op130 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op130 base (selected base ops) = @ExternalFuns.op130 base ops := rfl
#print axioms preserved_op130
theorem preserved_op131 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op131 base (selected base ops) = @ExternalFuns.op131 base ops := rfl
#print axioms preserved_op131
theorem preserved_op133 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op133 base (selected base ops) = @ExternalFuns.op133 base ops := rfl
#print axioms preserved_op133
theorem preserved_op134 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op134 base (selected base ops) = @ExternalFuns.op134 base ops := rfl
#print axioms preserved_op134
theorem preserved_op135 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op135 base (selected base ops) = @ExternalFuns.op135 base ops := rfl
#print axioms preserved_op135
theorem preserved_op136 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op136 base (selected base ops) = @ExternalFuns.op136 base ops := rfl
#print axioms preserved_op136
theorem preserved_op137 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op137 base (selected base ops) = @ExternalFuns.op137 base ops := rfl
#print axioms preserved_op137
theorem preserved_op138 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op138 base (selected base ops) = @ExternalFuns.op138 base ops := rfl
#print axioms preserved_op138
theorem preserved_op139 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op139 base (selected base ops) = @ExternalFuns.op139 base ops := rfl
#print axioms preserved_op139
theorem preserved_op140 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op140 base (selected base ops) = @ExternalFuns.op140 base ops := rfl
#print axioms preserved_op140
theorem preserved_op141 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op141 base (selected base ops) = @ExternalFuns.op141 base ops := rfl
#print axioms preserved_op141
theorem preserved_op142 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op142 base (selected base ops) = @ExternalFuns.op142 base ops := rfl
#print axioms preserved_op142
theorem preserved_op143 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op143 base (selected base ops) = @ExternalFuns.op143 base ops := rfl
#print axioms preserved_op143
theorem preserved_op144 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op144 base (selected base ops) = @ExternalFuns.op144 base ops := rfl
#print axioms preserved_op144
theorem preserved_op145 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op145 base (selected base ops) = @ExternalFuns.op145 base ops := rfl
#print axioms preserved_op145
theorem preserved_op146 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op146 base (selected base ops) = @ExternalFuns.op146 base ops := rfl
#print axioms preserved_op146
theorem preserved_op147 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op147 base (selected base ops) = @ExternalFuns.op147 base ops := rfl
#print axioms preserved_op147
theorem preserved_op148 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op148 base (selected base ops) = @ExternalFuns.op148 base ops := rfl
#print axioms preserved_op148
theorem preserved_op149 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op149 base (selected base ops) = @ExternalFuns.op149 base ops := rfl
#print axioms preserved_op149
theorem preserved_op150 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op150 base (selected base ops) = @ExternalFuns.op150 base ops := rfl
#print axioms preserved_op150
theorem preserved_op151 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op151 base (selected base ops) = @ExternalFuns.op151 base ops := rfl
#print axioms preserved_op151
theorem preserved_op152 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op152 base (selected base ops) = @ExternalFuns.op152 base ops := rfl
#print axioms preserved_op152
theorem preserved_op153 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op153 base (selected base ops) = @ExternalFuns.op153 base ops := rfl
#print axioms preserved_op153
theorem preserved_op154 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op154 base (selected base ops) = @ExternalFuns.op154 base ops := rfl
#print axioms preserved_op154
theorem preserved_op155 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op155 base (selected base ops) = @ExternalFuns.op155 base ops := rfl
#print axioms preserved_op155
theorem preserved_op156 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op156 base (selected base ops) = @ExternalFuns.op156 base ops := rfl
#print axioms preserved_op156
theorem preserved_op157 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op157 base (selected base ops) = @ExternalFuns.op157 base ops := rfl
#print axioms preserved_op157
theorem preserved_op158 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op158 base (selected base ops) = @ExternalFuns.op158 base ops := rfl
#print axioms preserved_op158
theorem preserved_op159 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op159 base (selected base ops) = @ExternalFuns.op159 base ops := rfl
#print axioms preserved_op159
theorem preserved_op160 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op160 base (selected base ops) = @ExternalFuns.op160 base ops := rfl
#print axioms preserved_op160
theorem preserved_op161 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op161 base (selected base ops) = @ExternalFuns.op161 base ops := rfl
#print axioms preserved_op161
theorem preserved_op162 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op162 base (selected base ops) = @ExternalFuns.op162 base ops := rfl
#print axioms preserved_op162
theorem preserved_op163 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op163 base (selected base ops) = @ExternalFuns.op163 base ops := rfl
#print axioms preserved_op163
theorem preserved_op164 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op164 base (selected base ops) = @ExternalFuns.op164 base ops := rfl
#print axioms preserved_op164
theorem preserved_op165 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op165 base (selected base ops) = @ExternalFuns.op165 base ops := rfl
#print axioms preserved_op165
theorem preserved_op166 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op166 base (selected base ops) = @ExternalFuns.op166 base ops := rfl
#print axioms preserved_op166
theorem preserved_op167 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op167 base (selected base ops) = @ExternalFuns.op167 base ops := rfl
#print axioms preserved_op167
theorem preserved_op168 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op168 base (selected base ops) = @ExternalFuns.op168 base ops := rfl
#print axioms preserved_op168
theorem preserved_op169 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op169 base (selected base ops) = @ExternalFuns.op169 base ops := rfl
#print axioms preserved_op169
theorem preserved_op170 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op170 base (selected base ops) = @ExternalFuns.op170 base ops := rfl
#print axioms preserved_op170
theorem preserved_op171 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op171 base (selected base ops) = @ExternalFuns.op171 base ops := rfl
#print axioms preserved_op171
theorem preserved_op172 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op172 base (selected base ops) = @ExternalFuns.op172 base ops := rfl
#print axioms preserved_op172
theorem preserved_op173 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op173 base (selected base ops) = @ExternalFuns.op173 base ops := rfl
#print axioms preserved_op173
theorem preserved_op174 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op174 base (selected base ops) = @ExternalFuns.op174 base ops := rfl
#print axioms preserved_op174
theorem preserved_op175 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op175 base (selected base ops) = @ExternalFuns.op175 base ops := rfl
#print axioms preserved_op175
theorem preserved_op176 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op176 base (selected base ops) = @ExternalFuns.op176 base ops := rfl
#print axioms preserved_op176
theorem preserved_op177 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op177 base (selected base ops) = @ExternalFuns.op177 base ops := rfl
#print axioms preserved_op177
theorem preserved_op178 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op178 base (selected base ops) = @ExternalFuns.op178 base ops := rfl
#print axioms preserved_op178
theorem preserved_op179 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op179 base (selected base ops) = @ExternalFuns.op179 base ops := rfl
#print axioms preserved_op179
theorem preserved_op180 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op180 base (selected base ops) = @ExternalFuns.op180 base ops := rfl
#print axioms preserved_op180
theorem preserved_op181 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op181 base (selected base ops) = @ExternalFuns.op181 base ops := rfl
#print axioms preserved_op181
theorem preserved_op182 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op182 base (selected base ops) = @ExternalFuns.op182 base ops := rfl
#print axioms preserved_op182
theorem preserved_op183 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op183 base (selected base ops) = @ExternalFuns.op183 base ops := rfl
#print axioms preserved_op183
theorem preserved_op184 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op184 base (selected base ops) = @ExternalFuns.op184 base ops := rfl
#print axioms preserved_op184
theorem preserved_op185 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op185 base (selected base ops) = @ExternalFuns.op185 base ops := rfl
#print axioms preserved_op185
theorem preserved_op186 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op186 base (selected base ops) = @ExternalFuns.op186 base ops := rfl
#print axioms preserved_op186
theorem preserved_op187 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op187 base (selected base ops) = @ExternalFuns.op187 base ops := rfl
#print axioms preserved_op187
theorem preserved_op188 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op188 base (selected base ops) = @ExternalFuns.op188 base ops := rfl
#print axioms preserved_op188
theorem preserved_op189 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op189 base (selected base ops) = @ExternalFuns.op189 base ops := rfl
#print axioms preserved_op189
theorem preserved_op190 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op190 base (selected base ops) = @ExternalFuns.op190 base ops := rfl
#print axioms preserved_op190
theorem preserved_op191 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op191 base (selected base ops) = @ExternalFuns.op191 base ops := rfl
#print axioms preserved_op191
theorem preserved_op192 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op192 base (selected base ops) = @ExternalFuns.op192 base ops := rfl
#print axioms preserved_op192
theorem preserved_op193 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op193 base (selected base ops) = @ExternalFuns.op193 base ops := rfl
#print axioms preserved_op193
theorem preserved_op194 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op194 base (selected base ops) = @ExternalFuns.op194 base ops := rfl
#print axioms preserved_op194
theorem preserved_op195 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op195 base (selected base ops) = @ExternalFuns.op195 base ops := rfl
#print axioms preserved_op195
theorem preserved_op196 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op196 base (selected base ops) = @ExternalFuns.op196 base ops := rfl
#print axioms preserved_op196
theorem preserved_op197 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op197 base (selected base ops) = @ExternalFuns.op197 base ops := rfl
#print axioms preserved_op197
theorem preserved_op198 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op198 base (selected base ops) = @ExternalFuns.op198 base ops := rfl
#print axioms preserved_op198
theorem preserved_op199 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op199 base (selected base ops) = @ExternalFuns.op199 base ops := rfl
#print axioms preserved_op199
theorem preserved_op200 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op200 base (selected base ops) = @ExternalFuns.op200 base ops := rfl
#print axioms preserved_op200
theorem preserved_op201 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op201 base (selected base ops) = @ExternalFuns.op201 base ops := rfl
#print axioms preserved_op201
theorem preserved_op202 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op202 base (selected base ops) = @ExternalFuns.op202 base ops := rfl
#print axioms preserved_op202
theorem preserved_op203 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op203 base (selected base ops) = @ExternalFuns.op203 base ops := rfl
#print axioms preserved_op203
theorem preserved_op204 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op204 base (selected base ops) = @ExternalFuns.op204 base ops := rfl
#print axioms preserved_op204
theorem preserved_op205 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op205 base (selected base ops) = @ExternalFuns.op205 base ops := rfl
#print axioms preserved_op205
theorem preserved_op206 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op206 base (selected base ops) = @ExternalFuns.op206 base ops := rfl
#print axioms preserved_op206
theorem preserved_op207 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op207 base (selected base ops) = @ExternalFuns.op207 base ops := rfl
#print axioms preserved_op207
theorem preserved_op208 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op208 base (selected base ops) = @ExternalFuns.op208 base ops := rfl
#print axioms preserved_op208
theorem preserved_op209 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op209 base (selected base ops) = @ExternalFuns.op209 base ops := rfl
#print axioms preserved_op209
theorem preserved_op210 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op210 base (selected base ops) = @ExternalFuns.op210 base ops := rfl
#print axioms preserved_op210
theorem preserved_op211 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op211 base (selected base ops) = @ExternalFuns.op211 base ops := rfl
#print axioms preserved_op211
theorem preserved_op212 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op212 base (selected base ops) = @ExternalFuns.op212 base ops := rfl
#print axioms preserved_op212
theorem preserved_op213 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op213 base (selected base ops) = @ExternalFuns.op213 base ops := rfl
#print axioms preserved_op213
theorem preserved_op214 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op214 base (selected base ops) = @ExternalFuns.op214 base ops := rfl
#print axioms preserved_op214
theorem preserved_op215 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op215 base (selected base ops) = @ExternalFuns.op215 base ops := rfl
#print axioms preserved_op215
theorem preserved_op216 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op216 base (selected base ops) = @ExternalFuns.op216 base ops := rfl
#print axioms preserved_op216
theorem preserved_op217 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op217 base (selected base ops) = @ExternalFuns.op217 base ops := rfl
#print axioms preserved_op217
theorem preserved_op218 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op218 base (selected base ops) = @ExternalFuns.op218 base ops := rfl
#print axioms preserved_op218
theorem preserved_op219 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op219 base (selected base ops) = @ExternalFuns.op219 base ops := rfl
#print axioms preserved_op219
theorem preserved_op220 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op220 base (selected base ops) = @ExternalFuns.op220 base ops := rfl
#print axioms preserved_op220
theorem preserved_op221 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op221 base (selected base ops) = @ExternalFuns.op221 base ops := rfl
#print axioms preserved_op221
theorem preserved_op222 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op222 base (selected base ops) = @ExternalFuns.op222 base ops := rfl
#print axioms preserved_op222
theorem preserved_op223 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op223 base (selected base ops) = @ExternalFuns.op223 base ops := rfl
#print axioms preserved_op223
theorem preserved_op224 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op224 base (selected base ops) = @ExternalFuns.op224 base ops := rfl
#print axioms preserved_op224
theorem preserved_op225 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op225 base (selected base ops) = @ExternalFuns.op225 base ops := rfl
#print axioms preserved_op225
theorem preserved_op226 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op226 base (selected base ops) = @ExternalFuns.op226 base ops := rfl
#print axioms preserved_op226
theorem preserved_op227 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op227 base (selected base ops) = @ExternalFuns.op227 base ops := rfl
#print axioms preserved_op227
theorem preserved_op228 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op228 base (selected base ops) = @ExternalFuns.op228 base ops := rfl
#print axioms preserved_op228
theorem preserved_op229 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op229 base (selected base ops) = @ExternalFuns.op229 base ops := rfl
#print axioms preserved_op229
theorem preserved_op230 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op230 base (selected base ops) = @ExternalFuns.op230 base ops := rfl
#print axioms preserved_op230
theorem preserved_op231 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op231 base (selected base ops) = @ExternalFuns.op231 base ops := rfl
#print axioms preserved_op231
theorem preserved_op232 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op232 base (selected base ops) = @ExternalFuns.op232 base ops := rfl
#print axioms preserved_op232
theorem preserved_op233 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op233 base (selected base ops) = @ExternalFuns.op233 base ops := rfl
#print axioms preserved_op233
theorem preserved_op234 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op234 base (selected base ops) = @ExternalFuns.op234 base ops := rfl
#print axioms preserved_op234
theorem preserved_op235 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op235 base (selected base ops) = @ExternalFuns.op235 base ops := rfl
#print axioms preserved_op235
theorem preserved_op236 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op236 base (selected base ops) = @ExternalFuns.op236 base ops := rfl
#print axioms preserved_op236
theorem preserved_op237 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op237 base (selected base ops) = @ExternalFuns.op237 base ops := rfl
#print axioms preserved_op237
theorem preserved_op238 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op238 base (selected base ops) = @ExternalFuns.op238 base ops := rfl
#print axioms preserved_op238
theorem preserved_op239 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op239 base (selected base ops) = @ExternalFuns.op239 base ops := rfl
#print axioms preserved_op239
theorem preserved_op240 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op240 base (selected base ops) = @ExternalFuns.op240 base ops := rfl
#print axioms preserved_op240
theorem preserved_op241 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op241 base (selected base ops) = @ExternalFuns.op241 base ops := rfl
#print axioms preserved_op241
theorem preserved_op242 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op242 base (selected base ops) = @ExternalFuns.op242 base ops := rfl
#print axioms preserved_op242
theorem preserved_op243 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op243 base (selected base ops) = @ExternalFuns.op243 base ops := rfl
#print axioms preserved_op243
theorem preserved_op244 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op244 base (selected base ops) = @ExternalFuns.op244 base ops := rfl
#print axioms preserved_op244
theorem preserved_op245 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op245 base (selected base ops) = @ExternalFuns.op245 base ops := rfl
#print axioms preserved_op245
theorem preserved_op246 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op246 base (selected base ops) = @ExternalFuns.op246 base ops := rfl
#print axioms preserved_op246
theorem preserved_op247 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op247 base (selected base ops) = @ExternalFuns.op247 base ops := rfl
#print axioms preserved_op247
theorem preserved_op248 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op248 base (selected base ops) = @ExternalFuns.op248 base ops := rfl
#print axioms preserved_op248
theorem preserved_op249 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op249 base (selected base ops) = @ExternalFuns.op249 base ops := rfl
#print axioms preserved_op249
theorem preserved_op250 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op250 base (selected base ops) = @ExternalFuns.op250 base ops := rfl
#print axioms preserved_op250
theorem preserved_op251 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op251 base (selected base ops) = @ExternalFuns.op251 base ops := rfl
#print axioms preserved_op251
theorem preserved_op252 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op252 base (selected base ops) = @ExternalFuns.op252 base ops := rfl
#print axioms preserved_op252
theorem preserved_op253 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op253 base (selected base ops) = @ExternalFuns.op253 base ops := rfl
#print axioms preserved_op253
theorem preserved_op254 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op254 base (selected base ops) = @ExternalFuns.op254 base ops := rfl
#print axioms preserved_op254
theorem preserved_op255 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op255 base (selected base ops) = @ExternalFuns.op255 base ops := rfl
#print axioms preserved_op255
theorem preserved_op256 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op256 base (selected base ops) = @ExternalFuns.op256 base ops := rfl
#print axioms preserved_op256
theorem preserved_op257 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op257 base (selected base ops) = @ExternalFuns.op257 base ops := rfl
#print axioms preserved_op257
theorem preserved_op258 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op258 base (selected base ops) = @ExternalFuns.op258 base ops := rfl
#print axioms preserved_op258
theorem preserved_op259 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op259 base (selected base ops) = @ExternalFuns.op259 base ops := rfl
#print axioms preserved_op259
theorem preserved_op260 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op260 base (selected base ops) = @ExternalFuns.op260 base ops := rfl
#print axioms preserved_op260
theorem preserved_op261 (base : ExternalTypes) (ops : @ExternalFuns base) :
    @ExternalFuns.op261 base (selected base ops) = @ExternalFuns.op261 base ops := rfl
#print axioms preserved_op261
end
end PV_B3P_Install132
