import R1Z.ProverRwFullExternalFuns
import PV_B3_MultilinearFinite222
import PV_B3_MultilinearGuard222
import PV_B3_ArrayCarrier
namespace PV_B3_Install222
open Aeneas Aeneas.Std Result ProverRwFull PV_B3_ArrayCarrier
set_option autoImplicit false
noncomputable section
abbrev NativeQ := ProverRwFull.aspis_core.field.QM31
abbrev CopyQ := PV_B3_Copy_222.aspis_core.field.QM31

def intoCopy (q : NativeQ) : CopyQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromCopy (q : CopyQ) : NativeQ := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def sliceMap {A B : Type} (f : A → B) (xs : Slice A) : Slice B :=
  ⟨xs.val.map f, by simpa only [List.length_map] using xs.property⟩

theorem roundtrip (q : NativeQ) : fromCopy (intoCopy q) = q := by
  cases q with | mk a b => cases a; cases b; rfl

def callback (column : Slice NativeQ) (point : Array NativeQ 10#usize) : Result (Option NativeQ) :=
  resultMap (Option.map fromCopy)
    (PV_B3_Copy_222.host_multilinear.multilinear_evaluate_qm31
      (sliceMap intoCopy column) (arrayMap intoCopy point))

def selected [ExternalTypes] (ops : ExternalFuns) : ExternalFuns := {ops with op222 := callback}

theorem source [ExternalTypes] (ops : ExternalFuns) (column : Slice NativeQ)
    (point : Array NativeQ 10#usize) :
    (selected ops).op222 column point = resultMap (Option.map fromCopy)
      (PV_B3_MultilinearFinite222.evaluate (sliceMap intoCopy column) (arrayMap intoCopy point)) := by
  change callback column point = _
  unfold callback
  rw [PV_B3_MultilinearFinite222.source]

def emptyColumn : Slice NativeQ := ⟨[], by decide⟩
theorem nonvacuity [ExternalTypes] (ops : ExternalFuns) (point : Array NativeQ 10#usize) :
    (selected ops).op222 emptyColumn point = ok none := by
  change callback emptyColumn point = _
  unfold callback
  rw [PV_B3_MultilinearGuard222.wrong_length _ _ (by decide)]
  rfl

#print axioms intoCopy
#print axioms fromCopy
#print axioms sliceMap
#print axioms roundtrip
#print axioms callback
#print axioms source
#print axioms nonvacuity
theorem preserved_op0 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op0 _ (selected ops) = @ExternalFuns.op0 _ ops := rfl
#print axioms preserved_op0
theorem preserved_op1 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op1 _ (selected ops) = @ExternalFuns.op1 _ ops := rfl
#print axioms preserved_op1
theorem preserved_op2 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op2 _ (selected ops) = @ExternalFuns.op2 _ ops := rfl
#print axioms preserved_op2
theorem preserved_op3 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op3 _ (selected ops) = @ExternalFuns.op3 _ ops := rfl
#print axioms preserved_op3
theorem preserved_op4 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op4 _ (selected ops) = @ExternalFuns.op4 _ ops := rfl
#print axioms preserved_op4
theorem preserved_op5 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op5 _ (selected ops) = @ExternalFuns.op5 _ ops := rfl
#print axioms preserved_op5
theorem preserved_op6 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op6 _ (selected ops) = @ExternalFuns.op6 _ ops := rfl
#print axioms preserved_op6
theorem preserved_op7 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op7 _ (selected ops) = @ExternalFuns.op7 _ ops := rfl
#print axioms preserved_op7
theorem preserved_op8 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op8 _ (selected ops) = @ExternalFuns.op8 _ ops := rfl
#print axioms preserved_op8
theorem preserved_op9 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op9 _ (selected ops) = @ExternalFuns.op9 _ ops := rfl
#print axioms preserved_op9
theorem preserved_op10 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op10 _ (selected ops) = @ExternalFuns.op10 _ ops := rfl
#print axioms preserved_op10
theorem preserved_op11 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op11 _ (selected ops) = @ExternalFuns.op11 _ ops := rfl
#print axioms preserved_op11
theorem preserved_op12 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op12 _ (selected ops) = @ExternalFuns.op12 _ ops := rfl
#print axioms preserved_op12
theorem preserved_op13 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op13 _ (selected ops) = @ExternalFuns.op13 _ ops := rfl
#print axioms preserved_op13
theorem preserved_op14 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op14 _ (selected ops) = @ExternalFuns.op14 _ ops := rfl
#print axioms preserved_op14
theorem preserved_op15 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op15 _ (selected ops) = @ExternalFuns.op15 _ ops := rfl
#print axioms preserved_op15
theorem preserved_op16 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op16 _ (selected ops) = @ExternalFuns.op16 _ ops := rfl
#print axioms preserved_op16
theorem preserved_op17 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op17 _ (selected ops) = @ExternalFuns.op17 _ ops := rfl
#print axioms preserved_op17
theorem preserved_op18 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op18 _ (selected ops) = @ExternalFuns.op18 _ ops := rfl
#print axioms preserved_op18
theorem preserved_op19 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op19 _ (selected ops) = @ExternalFuns.op19 _ ops := rfl
#print axioms preserved_op19
theorem preserved_op20 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op20 _ (selected ops) = @ExternalFuns.op20 _ ops := rfl
#print axioms preserved_op20
theorem preserved_op21 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op21 _ (selected ops) = @ExternalFuns.op21 _ ops := rfl
#print axioms preserved_op21
theorem preserved_op22 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op22 _ (selected ops) = @ExternalFuns.op22 _ ops := rfl
#print axioms preserved_op22
theorem preserved_op23 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op23 _ (selected ops) = @ExternalFuns.op23 _ ops := rfl
#print axioms preserved_op23
theorem preserved_op24 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op24 _ (selected ops) = @ExternalFuns.op24 _ ops := rfl
#print axioms preserved_op24
theorem preserved_op25 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op25 _ (selected ops) = @ExternalFuns.op25 _ ops := rfl
#print axioms preserved_op25
theorem preserved_op26 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op26 _ (selected ops) = @ExternalFuns.op26 _ ops := rfl
#print axioms preserved_op26
theorem preserved_op27 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op27 _ (selected ops) = @ExternalFuns.op27 _ ops := rfl
#print axioms preserved_op27
theorem preserved_op28 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op28 _ (selected ops) = @ExternalFuns.op28 _ ops := rfl
#print axioms preserved_op28
theorem preserved_op29 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op29 _ (selected ops) = @ExternalFuns.op29 _ ops := rfl
#print axioms preserved_op29
theorem preserved_op30 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op30 _ (selected ops) = @ExternalFuns.op30 _ ops := rfl
#print axioms preserved_op30
theorem preserved_op31 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op31 _ (selected ops) = @ExternalFuns.op31 _ ops := rfl
#print axioms preserved_op31
theorem preserved_op32 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op32 _ (selected ops) = @ExternalFuns.op32 _ ops := rfl
#print axioms preserved_op32
theorem preserved_op33 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op33 _ (selected ops) = @ExternalFuns.op33 _ ops := rfl
#print axioms preserved_op33
theorem preserved_op34 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op34 _ (selected ops) = @ExternalFuns.op34 _ ops := rfl
#print axioms preserved_op34
theorem preserved_op35 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op35 _ (selected ops) = @ExternalFuns.op35 _ ops := rfl
#print axioms preserved_op35
theorem preserved_op36 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op36 _ (selected ops) = @ExternalFuns.op36 _ ops := rfl
#print axioms preserved_op36
theorem preserved_op37 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op37 _ (selected ops) = @ExternalFuns.op37 _ ops := rfl
#print axioms preserved_op37
theorem preserved_op38 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op38 _ (selected ops) = @ExternalFuns.op38 _ ops := rfl
#print axioms preserved_op38
theorem preserved_op39 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op39 _ (selected ops) = @ExternalFuns.op39 _ ops := rfl
#print axioms preserved_op39
theorem preserved_op40 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op40 _ (selected ops) = @ExternalFuns.op40 _ ops := rfl
#print axioms preserved_op40
theorem preserved_op41 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op41 _ (selected ops) = @ExternalFuns.op41 _ ops := rfl
#print axioms preserved_op41
theorem preserved_op42 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op42 _ (selected ops) = @ExternalFuns.op42 _ ops := rfl
#print axioms preserved_op42
theorem preserved_op43 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op43 _ (selected ops) = @ExternalFuns.op43 _ ops := rfl
#print axioms preserved_op43
theorem preserved_op44 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op44 _ (selected ops) = @ExternalFuns.op44 _ ops := rfl
#print axioms preserved_op44
theorem preserved_op45 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op45 _ (selected ops) = @ExternalFuns.op45 _ ops := rfl
#print axioms preserved_op45
theorem preserved_op46 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op46 _ (selected ops) = @ExternalFuns.op46 _ ops := rfl
#print axioms preserved_op46
theorem preserved_op47 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op47 _ (selected ops) = @ExternalFuns.op47 _ ops := rfl
#print axioms preserved_op47
theorem preserved_op48 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op48 _ (selected ops) = @ExternalFuns.op48 _ ops := rfl
#print axioms preserved_op48
theorem preserved_op49 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op49 _ (selected ops) = @ExternalFuns.op49 _ ops := rfl
#print axioms preserved_op49
theorem preserved_op50 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op50 _ (selected ops) = @ExternalFuns.op50 _ ops := rfl
#print axioms preserved_op50
theorem preserved_op51 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op51 _ (selected ops) = @ExternalFuns.op51 _ ops := rfl
#print axioms preserved_op51
theorem preserved_op52 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op52 _ (selected ops) = @ExternalFuns.op52 _ ops := rfl
#print axioms preserved_op52
theorem preserved_op53 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op53 _ (selected ops) = @ExternalFuns.op53 _ ops := rfl
#print axioms preserved_op53
theorem preserved_op54 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op54 _ (selected ops) = @ExternalFuns.op54 _ ops := rfl
#print axioms preserved_op54
theorem preserved_op55 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op55 _ (selected ops) = @ExternalFuns.op55 _ ops := rfl
#print axioms preserved_op55
theorem preserved_op56 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op56 _ (selected ops) = @ExternalFuns.op56 _ ops := rfl
#print axioms preserved_op56
theorem preserved_op57 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op57 _ (selected ops) = @ExternalFuns.op57 _ ops := rfl
#print axioms preserved_op57
theorem preserved_op58 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op58 _ (selected ops) = @ExternalFuns.op58 _ ops := rfl
#print axioms preserved_op58
theorem preserved_op59 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op59 _ (selected ops) = @ExternalFuns.op59 _ ops := rfl
#print axioms preserved_op59
theorem preserved_op60 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op60 _ (selected ops) = @ExternalFuns.op60 _ ops := rfl
#print axioms preserved_op60
theorem preserved_op61 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op61 _ (selected ops) = @ExternalFuns.op61 _ ops := rfl
#print axioms preserved_op61
theorem preserved_op62 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op62 _ (selected ops) = @ExternalFuns.op62 _ ops := rfl
#print axioms preserved_op62
theorem preserved_op63 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op63 _ (selected ops) = @ExternalFuns.op63 _ ops := rfl
#print axioms preserved_op63
theorem preserved_op64 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op64 _ (selected ops) = @ExternalFuns.op64 _ ops := rfl
#print axioms preserved_op64
theorem preserved_op65 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op65 _ (selected ops) = @ExternalFuns.op65 _ ops := rfl
#print axioms preserved_op65
theorem preserved_op66 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op66 _ (selected ops) = @ExternalFuns.op66 _ ops := rfl
#print axioms preserved_op66
theorem preserved_op67 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op67 _ (selected ops) = @ExternalFuns.op67 _ ops := rfl
#print axioms preserved_op67
theorem preserved_op68 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op68 _ (selected ops) = @ExternalFuns.op68 _ ops := rfl
#print axioms preserved_op68
theorem preserved_op69 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op69 _ (selected ops) = @ExternalFuns.op69 _ ops := rfl
#print axioms preserved_op69
theorem preserved_op70 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op70 _ (selected ops) = @ExternalFuns.op70 _ ops := rfl
#print axioms preserved_op70
theorem preserved_op71 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op71 _ (selected ops) = @ExternalFuns.op71 _ ops := rfl
#print axioms preserved_op71
theorem preserved_op72 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op72 _ (selected ops) = @ExternalFuns.op72 _ ops := rfl
#print axioms preserved_op72
theorem preserved_op73 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op73 _ (selected ops) = @ExternalFuns.op73 _ ops := rfl
#print axioms preserved_op73
theorem preserved_op74 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op74 _ (selected ops) = @ExternalFuns.op74 _ ops := rfl
#print axioms preserved_op74
theorem preserved_op75 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op75 _ (selected ops) = @ExternalFuns.op75 _ ops := rfl
#print axioms preserved_op75
theorem preserved_op76 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op76 _ (selected ops) = @ExternalFuns.op76 _ ops := rfl
#print axioms preserved_op76
theorem preserved_op77 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op77 _ (selected ops) = @ExternalFuns.op77 _ ops := rfl
#print axioms preserved_op77
theorem preserved_op78 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op78 _ (selected ops) = @ExternalFuns.op78 _ ops := rfl
#print axioms preserved_op78
theorem preserved_op79 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op79 _ (selected ops) = @ExternalFuns.op79 _ ops := rfl
#print axioms preserved_op79
theorem preserved_op80 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op80 _ (selected ops) = @ExternalFuns.op80 _ ops := rfl
#print axioms preserved_op80
theorem preserved_op81 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op81 _ (selected ops) = @ExternalFuns.op81 _ ops := rfl
#print axioms preserved_op81
theorem preserved_op82 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op82 _ (selected ops) = @ExternalFuns.op82 _ ops := rfl
#print axioms preserved_op82
theorem preserved_op83 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op83 _ (selected ops) = @ExternalFuns.op83 _ ops := rfl
#print axioms preserved_op83
theorem preserved_op84 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op84 _ (selected ops) = @ExternalFuns.op84 _ ops := rfl
#print axioms preserved_op84
theorem preserved_op85 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op85 _ (selected ops) = @ExternalFuns.op85 _ ops := rfl
#print axioms preserved_op85
theorem preserved_op86 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op86 _ (selected ops) = @ExternalFuns.op86 _ ops := rfl
#print axioms preserved_op86
theorem preserved_op87 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op87 _ (selected ops) = @ExternalFuns.op87 _ ops := rfl
#print axioms preserved_op87
theorem preserved_op88 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op88 _ (selected ops) = @ExternalFuns.op88 _ ops := rfl
#print axioms preserved_op88
theorem preserved_op89 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op89 _ (selected ops) = @ExternalFuns.op89 _ ops := rfl
#print axioms preserved_op89
theorem preserved_op90 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op90 _ (selected ops) = @ExternalFuns.op90 _ ops := rfl
#print axioms preserved_op90
theorem preserved_op91 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op91 _ (selected ops) = @ExternalFuns.op91 _ ops := rfl
#print axioms preserved_op91
theorem preserved_op92 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op92 _ (selected ops) = @ExternalFuns.op92 _ ops := rfl
#print axioms preserved_op92
theorem preserved_op93 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op93 _ (selected ops) = @ExternalFuns.op93 _ ops := rfl
#print axioms preserved_op93
theorem preserved_op94 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op94 _ (selected ops) = @ExternalFuns.op94 _ ops := rfl
#print axioms preserved_op94
theorem preserved_op95 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op95 _ (selected ops) = @ExternalFuns.op95 _ ops := rfl
#print axioms preserved_op95
theorem preserved_op96 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op96 _ (selected ops) = @ExternalFuns.op96 _ ops := rfl
#print axioms preserved_op96
theorem preserved_op97 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op97 _ (selected ops) = @ExternalFuns.op97 _ ops := rfl
#print axioms preserved_op97
theorem preserved_op98 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op98 _ (selected ops) = @ExternalFuns.op98 _ ops := rfl
#print axioms preserved_op98
theorem preserved_op99 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op99 _ (selected ops) = @ExternalFuns.op99 _ ops := rfl
#print axioms preserved_op99
theorem preserved_op100 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op100 _ (selected ops) = @ExternalFuns.op100 _ ops := rfl
#print axioms preserved_op100
theorem preserved_op101 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op101 _ (selected ops) = @ExternalFuns.op101 _ ops := rfl
#print axioms preserved_op101
theorem preserved_op102 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op102 _ (selected ops) = @ExternalFuns.op102 _ ops := rfl
#print axioms preserved_op102
theorem preserved_op103 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op103 _ (selected ops) = @ExternalFuns.op103 _ ops := rfl
#print axioms preserved_op103
theorem preserved_op104 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op104 _ (selected ops) = @ExternalFuns.op104 _ ops := rfl
#print axioms preserved_op104
theorem preserved_op105 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op105 _ (selected ops) = @ExternalFuns.op105 _ ops := rfl
#print axioms preserved_op105
theorem preserved_op106 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op106 _ (selected ops) = @ExternalFuns.op106 _ ops := rfl
#print axioms preserved_op106
theorem preserved_op107 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op107 _ (selected ops) = @ExternalFuns.op107 _ ops := rfl
#print axioms preserved_op107
theorem preserved_op108 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op108 _ (selected ops) = @ExternalFuns.op108 _ ops := rfl
#print axioms preserved_op108
theorem preserved_op109 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op109 _ (selected ops) = @ExternalFuns.op109 _ ops := rfl
#print axioms preserved_op109
theorem preserved_op110 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op110 _ (selected ops) = @ExternalFuns.op110 _ ops := rfl
#print axioms preserved_op110
theorem preserved_op111 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op111 _ (selected ops) = @ExternalFuns.op111 _ ops := rfl
#print axioms preserved_op111
theorem preserved_op112 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op112 _ (selected ops) = @ExternalFuns.op112 _ ops := rfl
#print axioms preserved_op112
theorem preserved_op113 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op113 _ (selected ops) = @ExternalFuns.op113 _ ops := rfl
#print axioms preserved_op113
theorem preserved_op114 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op114 _ (selected ops) = @ExternalFuns.op114 _ ops := rfl
#print axioms preserved_op114
theorem preserved_op115 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op115 _ (selected ops) = @ExternalFuns.op115 _ ops := rfl
#print axioms preserved_op115
theorem preserved_op116 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op116 _ (selected ops) = @ExternalFuns.op116 _ ops := rfl
#print axioms preserved_op116
theorem preserved_op117 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op117 _ (selected ops) = @ExternalFuns.op117 _ ops := rfl
#print axioms preserved_op117
theorem preserved_op118 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op118 _ (selected ops) = @ExternalFuns.op118 _ ops := rfl
#print axioms preserved_op118
theorem preserved_op119 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op119 _ (selected ops) = @ExternalFuns.op119 _ ops := rfl
#print axioms preserved_op119
theorem preserved_op120 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op120 _ (selected ops) = @ExternalFuns.op120 _ ops := rfl
#print axioms preserved_op120
theorem preserved_op121 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op121 _ (selected ops) = @ExternalFuns.op121 _ ops := rfl
#print axioms preserved_op121
theorem preserved_op122 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op122 _ (selected ops) = @ExternalFuns.op122 _ ops := rfl
#print axioms preserved_op122
theorem preserved_op123 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op123 _ (selected ops) = @ExternalFuns.op123 _ ops := rfl
#print axioms preserved_op123
theorem preserved_op124 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op124 _ (selected ops) = @ExternalFuns.op124 _ ops := rfl
#print axioms preserved_op124
theorem preserved_op125 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op125 _ (selected ops) = @ExternalFuns.op125 _ ops := rfl
#print axioms preserved_op125
theorem preserved_op126 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op126 _ (selected ops) = @ExternalFuns.op126 _ ops := rfl
#print axioms preserved_op126
theorem preserved_op127 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op127 _ (selected ops) = @ExternalFuns.op127 _ ops := rfl
#print axioms preserved_op127
theorem preserved_op128 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op128 _ (selected ops) = @ExternalFuns.op128 _ ops := rfl
#print axioms preserved_op128
theorem preserved_op129 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op129 _ (selected ops) = @ExternalFuns.op129 _ ops := rfl
#print axioms preserved_op129
theorem preserved_op130 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op130 _ (selected ops) = @ExternalFuns.op130 _ ops := rfl
#print axioms preserved_op130
theorem preserved_op131 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op131 _ (selected ops) = @ExternalFuns.op131 _ ops := rfl
#print axioms preserved_op131
theorem preserved_op132 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op132 _ (selected ops) = @ExternalFuns.op132 _ ops := rfl
#print axioms preserved_op132
theorem preserved_op133 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op133 _ (selected ops) = @ExternalFuns.op133 _ ops := rfl
#print axioms preserved_op133
theorem preserved_op134 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op134 _ (selected ops) = @ExternalFuns.op134 _ ops := rfl
#print axioms preserved_op134
theorem preserved_op135 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op135 _ (selected ops) = @ExternalFuns.op135 _ ops := rfl
#print axioms preserved_op135
theorem preserved_op136 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op136 _ (selected ops) = @ExternalFuns.op136 _ ops := rfl
#print axioms preserved_op136
theorem preserved_op137 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op137 _ (selected ops) = @ExternalFuns.op137 _ ops := rfl
#print axioms preserved_op137
theorem preserved_op138 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op138 _ (selected ops) = @ExternalFuns.op138 _ ops := rfl
#print axioms preserved_op138
theorem preserved_op139 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op139 _ (selected ops) = @ExternalFuns.op139 _ ops := rfl
#print axioms preserved_op139
theorem preserved_op140 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op140 _ (selected ops) = @ExternalFuns.op140 _ ops := rfl
#print axioms preserved_op140
theorem preserved_op141 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op141 _ (selected ops) = @ExternalFuns.op141 _ ops := rfl
#print axioms preserved_op141
theorem preserved_op142 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op142 _ (selected ops) = @ExternalFuns.op142 _ ops := rfl
#print axioms preserved_op142
theorem preserved_op143 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op143 _ (selected ops) = @ExternalFuns.op143 _ ops := rfl
#print axioms preserved_op143
theorem preserved_op144 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op144 _ (selected ops) = @ExternalFuns.op144 _ ops := rfl
#print axioms preserved_op144
theorem preserved_op145 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op145 _ (selected ops) = @ExternalFuns.op145 _ ops := rfl
#print axioms preserved_op145
theorem preserved_op146 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op146 _ (selected ops) = @ExternalFuns.op146 _ ops := rfl
#print axioms preserved_op146
theorem preserved_op147 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op147 _ (selected ops) = @ExternalFuns.op147 _ ops := rfl
#print axioms preserved_op147
theorem preserved_op148 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op148 _ (selected ops) = @ExternalFuns.op148 _ ops := rfl
#print axioms preserved_op148
theorem preserved_op149 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op149 _ (selected ops) = @ExternalFuns.op149 _ ops := rfl
#print axioms preserved_op149
theorem preserved_op150 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op150 _ (selected ops) = @ExternalFuns.op150 _ ops := rfl
#print axioms preserved_op150
theorem preserved_op151 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op151 _ (selected ops) = @ExternalFuns.op151 _ ops := rfl
#print axioms preserved_op151
theorem preserved_op152 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op152 _ (selected ops) = @ExternalFuns.op152 _ ops := rfl
#print axioms preserved_op152
theorem preserved_op153 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op153 _ (selected ops) = @ExternalFuns.op153 _ ops := rfl
#print axioms preserved_op153
theorem preserved_op154 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op154 _ (selected ops) = @ExternalFuns.op154 _ ops := rfl
#print axioms preserved_op154
theorem preserved_op155 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op155 _ (selected ops) = @ExternalFuns.op155 _ ops := rfl
#print axioms preserved_op155
theorem preserved_op156 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op156 _ (selected ops) = @ExternalFuns.op156 _ ops := rfl
#print axioms preserved_op156
theorem preserved_op157 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op157 _ (selected ops) = @ExternalFuns.op157 _ ops := rfl
#print axioms preserved_op157
theorem preserved_op158 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op158 _ (selected ops) = @ExternalFuns.op158 _ ops := rfl
#print axioms preserved_op158
theorem preserved_op159 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op159 _ (selected ops) = @ExternalFuns.op159 _ ops := rfl
#print axioms preserved_op159
theorem preserved_op160 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op160 _ (selected ops) = @ExternalFuns.op160 _ ops := rfl
#print axioms preserved_op160
theorem preserved_op161 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op161 _ (selected ops) = @ExternalFuns.op161 _ ops := rfl
#print axioms preserved_op161
theorem preserved_op162 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op162 _ (selected ops) = @ExternalFuns.op162 _ ops := rfl
#print axioms preserved_op162
theorem preserved_op163 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op163 _ (selected ops) = @ExternalFuns.op163 _ ops := rfl
#print axioms preserved_op163
theorem preserved_op164 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op164 _ (selected ops) = @ExternalFuns.op164 _ ops := rfl
#print axioms preserved_op164
theorem preserved_op165 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op165 _ (selected ops) = @ExternalFuns.op165 _ ops := rfl
#print axioms preserved_op165
theorem preserved_op166 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op166 _ (selected ops) = @ExternalFuns.op166 _ ops := rfl
#print axioms preserved_op166
theorem preserved_op167 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op167 _ (selected ops) = @ExternalFuns.op167 _ ops := rfl
#print axioms preserved_op167
theorem preserved_op168 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op168 _ (selected ops) = @ExternalFuns.op168 _ ops := rfl
#print axioms preserved_op168
theorem preserved_op169 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op169 _ (selected ops) = @ExternalFuns.op169 _ ops := rfl
#print axioms preserved_op169
theorem preserved_op170 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op170 _ (selected ops) = @ExternalFuns.op170 _ ops := rfl
#print axioms preserved_op170
theorem preserved_op171 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op171 _ (selected ops) = @ExternalFuns.op171 _ ops := rfl
#print axioms preserved_op171
theorem preserved_op172 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op172 _ (selected ops) = @ExternalFuns.op172 _ ops := rfl
#print axioms preserved_op172
theorem preserved_op173 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op173 _ (selected ops) = @ExternalFuns.op173 _ ops := rfl
#print axioms preserved_op173
theorem preserved_op174 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op174 _ (selected ops) = @ExternalFuns.op174 _ ops := rfl
#print axioms preserved_op174
theorem preserved_op175 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op175 _ (selected ops) = @ExternalFuns.op175 _ ops := rfl
#print axioms preserved_op175
theorem preserved_op176 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op176 _ (selected ops) = @ExternalFuns.op176 _ ops := rfl
#print axioms preserved_op176
theorem preserved_op177 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op177 _ (selected ops) = @ExternalFuns.op177 _ ops := rfl
#print axioms preserved_op177
theorem preserved_op178 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op178 _ (selected ops) = @ExternalFuns.op178 _ ops := rfl
#print axioms preserved_op178
theorem preserved_op179 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op179 _ (selected ops) = @ExternalFuns.op179 _ ops := rfl
#print axioms preserved_op179
theorem preserved_op180 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op180 _ (selected ops) = @ExternalFuns.op180 _ ops := rfl
#print axioms preserved_op180
theorem preserved_op181 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op181 _ (selected ops) = @ExternalFuns.op181 _ ops := rfl
#print axioms preserved_op181
theorem preserved_op182 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op182 _ (selected ops) = @ExternalFuns.op182 _ ops := rfl
#print axioms preserved_op182
theorem preserved_op183 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op183 _ (selected ops) = @ExternalFuns.op183 _ ops := rfl
#print axioms preserved_op183
theorem preserved_op184 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op184 _ (selected ops) = @ExternalFuns.op184 _ ops := rfl
#print axioms preserved_op184
theorem preserved_op185 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op185 _ (selected ops) = @ExternalFuns.op185 _ ops := rfl
#print axioms preserved_op185
theorem preserved_op186 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op186 _ (selected ops) = @ExternalFuns.op186 _ ops := rfl
#print axioms preserved_op186
theorem preserved_op187 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op187 _ (selected ops) = @ExternalFuns.op187 _ ops := rfl
#print axioms preserved_op187
theorem preserved_op188 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op188 _ (selected ops) = @ExternalFuns.op188 _ ops := rfl
#print axioms preserved_op188
theorem preserved_op189 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op189 _ (selected ops) = @ExternalFuns.op189 _ ops := rfl
#print axioms preserved_op189
theorem preserved_op190 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op190 _ (selected ops) = @ExternalFuns.op190 _ ops := rfl
#print axioms preserved_op190
theorem preserved_op191 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op191 _ (selected ops) = @ExternalFuns.op191 _ ops := rfl
#print axioms preserved_op191
theorem preserved_op192 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op192 _ (selected ops) = @ExternalFuns.op192 _ ops := rfl
#print axioms preserved_op192
theorem preserved_op193 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op193 _ (selected ops) = @ExternalFuns.op193 _ ops := rfl
#print axioms preserved_op193
theorem preserved_op194 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op194 _ (selected ops) = @ExternalFuns.op194 _ ops := rfl
#print axioms preserved_op194
theorem preserved_op195 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op195 _ (selected ops) = @ExternalFuns.op195 _ ops := rfl
#print axioms preserved_op195
theorem preserved_op196 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op196 _ (selected ops) = @ExternalFuns.op196 _ ops := rfl
#print axioms preserved_op196
theorem preserved_op197 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op197 _ (selected ops) = @ExternalFuns.op197 _ ops := rfl
#print axioms preserved_op197
theorem preserved_op198 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op198 _ (selected ops) = @ExternalFuns.op198 _ ops := rfl
#print axioms preserved_op198
theorem preserved_op199 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op199 _ (selected ops) = @ExternalFuns.op199 _ ops := rfl
#print axioms preserved_op199
theorem preserved_op200 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op200 _ (selected ops) = @ExternalFuns.op200 _ ops := rfl
#print axioms preserved_op200
theorem preserved_op201 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op201 _ (selected ops) = @ExternalFuns.op201 _ ops := rfl
#print axioms preserved_op201
theorem preserved_op202 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op202 _ (selected ops) = @ExternalFuns.op202 _ ops := rfl
#print axioms preserved_op202
theorem preserved_op203 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op203 _ (selected ops) = @ExternalFuns.op203 _ ops := rfl
#print axioms preserved_op203
theorem preserved_op204 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op204 _ (selected ops) = @ExternalFuns.op204 _ ops := rfl
#print axioms preserved_op204
theorem preserved_op205 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op205 _ (selected ops) = @ExternalFuns.op205 _ ops := rfl
#print axioms preserved_op205
theorem preserved_op206 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op206 _ (selected ops) = @ExternalFuns.op206 _ ops := rfl
#print axioms preserved_op206
theorem preserved_op207 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op207 _ (selected ops) = @ExternalFuns.op207 _ ops := rfl
#print axioms preserved_op207
theorem preserved_op208 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op208 _ (selected ops) = @ExternalFuns.op208 _ ops := rfl
#print axioms preserved_op208
theorem preserved_op209 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op209 _ (selected ops) = @ExternalFuns.op209 _ ops := rfl
#print axioms preserved_op209
theorem preserved_op210 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op210 _ (selected ops) = @ExternalFuns.op210 _ ops := rfl
#print axioms preserved_op210
theorem preserved_op211 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op211 _ (selected ops) = @ExternalFuns.op211 _ ops := rfl
#print axioms preserved_op211
theorem preserved_op212 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op212 _ (selected ops) = @ExternalFuns.op212 _ ops := rfl
#print axioms preserved_op212
theorem preserved_op213 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op213 _ (selected ops) = @ExternalFuns.op213 _ ops := rfl
#print axioms preserved_op213
theorem preserved_op214 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op214 _ (selected ops) = @ExternalFuns.op214 _ ops := rfl
#print axioms preserved_op214
theorem preserved_op215 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op215 _ (selected ops) = @ExternalFuns.op215 _ ops := rfl
#print axioms preserved_op215
theorem preserved_op216 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op216 _ (selected ops) = @ExternalFuns.op216 _ ops := rfl
#print axioms preserved_op216
theorem preserved_op217 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op217 _ (selected ops) = @ExternalFuns.op217 _ ops := rfl
#print axioms preserved_op217
theorem preserved_op218 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op218 _ (selected ops) = @ExternalFuns.op218 _ ops := rfl
#print axioms preserved_op218
theorem preserved_op219 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op219 _ (selected ops) = @ExternalFuns.op219 _ ops := rfl
#print axioms preserved_op219
theorem preserved_op220 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op220 _ (selected ops) = @ExternalFuns.op220 _ ops := rfl
#print axioms preserved_op220
theorem preserved_op221 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op221 _ (selected ops) = @ExternalFuns.op221 _ ops := rfl
#print axioms preserved_op221
theorem preserved_op223 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op223 _ (selected ops) = @ExternalFuns.op223 _ ops := rfl
#print axioms preserved_op223
theorem preserved_op224 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op224 _ (selected ops) = @ExternalFuns.op224 _ ops := rfl
#print axioms preserved_op224
theorem preserved_op225 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op225 _ (selected ops) = @ExternalFuns.op225 _ ops := rfl
#print axioms preserved_op225
theorem preserved_op226 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op226 _ (selected ops) = @ExternalFuns.op226 _ ops := rfl
#print axioms preserved_op226
theorem preserved_op227 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op227 _ (selected ops) = @ExternalFuns.op227 _ ops := rfl
#print axioms preserved_op227
theorem preserved_op228 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op228 _ (selected ops) = @ExternalFuns.op228 _ ops := rfl
#print axioms preserved_op228
theorem preserved_op229 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op229 _ (selected ops) = @ExternalFuns.op229 _ ops := rfl
#print axioms preserved_op229
theorem preserved_op230 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op230 _ (selected ops) = @ExternalFuns.op230 _ ops := rfl
#print axioms preserved_op230
theorem preserved_op231 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op231 _ (selected ops) = @ExternalFuns.op231 _ ops := rfl
#print axioms preserved_op231
theorem preserved_op232 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op232 _ (selected ops) = @ExternalFuns.op232 _ ops := rfl
#print axioms preserved_op232
theorem preserved_op233 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op233 _ (selected ops) = @ExternalFuns.op233 _ ops := rfl
#print axioms preserved_op233
theorem preserved_op234 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op234 _ (selected ops) = @ExternalFuns.op234 _ ops := rfl
#print axioms preserved_op234
theorem preserved_op235 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op235 _ (selected ops) = @ExternalFuns.op235 _ ops := rfl
#print axioms preserved_op235
theorem preserved_op236 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op236 _ (selected ops) = @ExternalFuns.op236 _ ops := rfl
#print axioms preserved_op236
theorem preserved_op237 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op237 _ (selected ops) = @ExternalFuns.op237 _ ops := rfl
#print axioms preserved_op237
theorem preserved_op238 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op238 _ (selected ops) = @ExternalFuns.op238 _ ops := rfl
#print axioms preserved_op238
theorem preserved_op239 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op239 _ (selected ops) = @ExternalFuns.op239 _ ops := rfl
#print axioms preserved_op239
theorem preserved_op240 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op240 _ (selected ops) = @ExternalFuns.op240 _ ops := rfl
#print axioms preserved_op240
theorem preserved_op241 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op241 _ (selected ops) = @ExternalFuns.op241 _ ops := rfl
#print axioms preserved_op241
theorem preserved_op242 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op242 _ (selected ops) = @ExternalFuns.op242 _ ops := rfl
#print axioms preserved_op242
theorem preserved_op243 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op243 _ (selected ops) = @ExternalFuns.op243 _ ops := rfl
#print axioms preserved_op243
theorem preserved_op244 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op244 _ (selected ops) = @ExternalFuns.op244 _ ops := rfl
#print axioms preserved_op244
theorem preserved_op245 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op245 _ (selected ops) = @ExternalFuns.op245 _ ops := rfl
#print axioms preserved_op245
theorem preserved_op246 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op246 _ (selected ops) = @ExternalFuns.op246 _ ops := rfl
#print axioms preserved_op246
theorem preserved_op247 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op247 _ (selected ops) = @ExternalFuns.op247 _ ops := rfl
#print axioms preserved_op247
theorem preserved_op248 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op248 _ (selected ops) = @ExternalFuns.op248 _ ops := rfl
#print axioms preserved_op248
theorem preserved_op249 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op249 _ (selected ops) = @ExternalFuns.op249 _ ops := rfl
#print axioms preserved_op249
theorem preserved_op250 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op250 _ (selected ops) = @ExternalFuns.op250 _ ops := rfl
#print axioms preserved_op250
theorem preserved_op251 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op251 _ (selected ops) = @ExternalFuns.op251 _ ops := rfl
#print axioms preserved_op251
theorem preserved_op252 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op252 _ (selected ops) = @ExternalFuns.op252 _ ops := rfl
#print axioms preserved_op252
theorem preserved_op253 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op253 _ (selected ops) = @ExternalFuns.op253 _ ops := rfl
#print axioms preserved_op253
theorem preserved_op254 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op254 _ (selected ops) = @ExternalFuns.op254 _ ops := rfl
#print axioms preserved_op254
theorem preserved_op255 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op255 _ (selected ops) = @ExternalFuns.op255 _ ops := rfl
#print axioms preserved_op255
theorem preserved_op256 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op256 _ (selected ops) = @ExternalFuns.op256 _ ops := rfl
#print axioms preserved_op256
theorem preserved_op257 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op257 _ (selected ops) = @ExternalFuns.op257 _ ops := rfl
#print axioms preserved_op257
theorem preserved_op258 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op258 _ (selected ops) = @ExternalFuns.op258 _ ops := rfl
#print axioms preserved_op258
theorem preserved_op259 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op259 _ (selected ops) = @ExternalFuns.op259 _ ops := rfl
#print axioms preserved_op259
theorem preserved_op260 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op260 _ (selected ops) = @ExternalFuns.op260 _ ops := rfl
#print axioms preserved_op260
theorem preserved_op261 [ExternalTypes] (ops : ExternalFuns) :
    @ExternalFuns.op261 _ (selected ops) = @ExternalFuns.op261 _ ops := rfl
#print axioms preserved_op261
end
end PV_B3_Install222
