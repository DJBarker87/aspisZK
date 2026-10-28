import PV_B3P_PublicCarrier226V3
import PV_B3P_ByteOutput226
import PV_B3P_BytesV3Emission226
namespace PV_B3P_Install226V3
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
noncomputable section
abbrev Types := PV_B3P_PublicCarrier226V3.Types
abbrev E := PV_B3P_226V3.aspis_core.state_only_prefix.r0.Error
abbrev Packet := (PV_B3P_ByteOutput226.Chunks × Usize)

def transport : Result (core.result.Result Packet E) →
    Result (core.result.Result (alloc.vec.Vec U8) E)
  | .ok (.Ok (chunks,n)) => .ok (.Ok (PV_B3P_ByteOutput226.bytes chunks n))
  | .ok (.Err e) => .ok (.Err e)
  | .fail e => .fail e
  | .div => .div

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {ops with op226 := fun p => transport (PV_B3P_226V3.reference226.public_bytes (PV_B3P_PublicCarrier226V3.toSource base p))}

theorem source (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base)) :
    @ExternalFuns.op226 (Types base) (selected base ops) p =
      transport (PV_B3P_226V3.reference226.public_bytes
        (PV_B3P_PublicCarrier226V3.toSource base p)) := rfl

theorem source_complete (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (p : @aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public (Types base)) :
    @ExternalFuns.op226 (Types base) (selected base ops) p = (do
      let projected ← PV_B3P_226V3.reference226.project (PV_B3P_PublicCarrier226V3.toSource base p)
      transport (PV_B3P_226V3.reference226.encode_owned projected)) := by
  rw [source]
  unfold PV_B3P_226V3.reference226.public_bytes
  cases PV_B3P_226V3.reference226.project (PV_B3P_PublicCarrier226V3.toSource base p) <;> rfl

theorem error_tag (e : E) : transport (.ok (.Err e)) = .ok (.Err e) := rfl
theorem fail_tag (e : Aeneas.Std.Error) : transport (.fail e) = .fail e := rfl
theorem div_tag : transport .div = .div := rfl

#print axioms source
#print axioms source_complete
#print axioms error_tag
#print axioms fail_tag
#print axioms div_tag
theorem preserved_op0 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op0 (Types base) (selected base ops) = @ExternalFuns.op0 (Types base) ops := rfl
#print axioms preserved_op0
theorem preserved_op1 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op1 (Types base) (selected base ops) = @ExternalFuns.op1 (Types base) ops := rfl
#print axioms preserved_op1
theorem preserved_op2 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op2 (Types base) (selected base ops) = @ExternalFuns.op2 (Types base) ops := rfl
#print axioms preserved_op2
theorem preserved_op3 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op3 (Types base) (selected base ops) = @ExternalFuns.op3 (Types base) ops := rfl
#print axioms preserved_op3
theorem preserved_op4 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op4 (Types base) (selected base ops) = @ExternalFuns.op4 (Types base) ops := rfl
#print axioms preserved_op4
theorem preserved_op5 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op5 (Types base) (selected base ops) = @ExternalFuns.op5 (Types base) ops := rfl
#print axioms preserved_op5
theorem preserved_op6 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op6 (Types base) (selected base ops) = @ExternalFuns.op6 (Types base) ops := rfl
#print axioms preserved_op6
theorem preserved_op7 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op7 (Types base) (selected base ops) = @ExternalFuns.op7 (Types base) ops := rfl
#print axioms preserved_op7
theorem preserved_op8 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op8 (Types base) (selected base ops) = @ExternalFuns.op8 (Types base) ops := rfl
#print axioms preserved_op8
theorem preserved_op9 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op9 (Types base) (selected base ops) = @ExternalFuns.op9 (Types base) ops := rfl
#print axioms preserved_op9
theorem preserved_op10 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op10 (Types base) (selected base ops) = @ExternalFuns.op10 (Types base) ops := rfl
#print axioms preserved_op10
theorem preserved_op11 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op11 (Types base) (selected base ops) = @ExternalFuns.op11 (Types base) ops := rfl
#print axioms preserved_op11
theorem preserved_op12 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op12 (Types base) (selected base ops) = @ExternalFuns.op12 (Types base) ops := rfl
#print axioms preserved_op12
theorem preserved_op13 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op13 (Types base) (selected base ops) = @ExternalFuns.op13 (Types base) ops := rfl
#print axioms preserved_op13
theorem preserved_op14 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op14 (Types base) (selected base ops) = @ExternalFuns.op14 (Types base) ops := rfl
#print axioms preserved_op14
theorem preserved_op15 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op15 (Types base) (selected base ops) = @ExternalFuns.op15 (Types base) ops := rfl
#print axioms preserved_op15
theorem preserved_op16 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op16 (Types base) (selected base ops) = @ExternalFuns.op16 (Types base) ops := rfl
#print axioms preserved_op16
theorem preserved_op17 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op17 (Types base) (selected base ops) = @ExternalFuns.op17 (Types base) ops := rfl
#print axioms preserved_op17
theorem preserved_op18 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op18 (Types base) (selected base ops) = @ExternalFuns.op18 (Types base) ops := rfl
#print axioms preserved_op18
theorem preserved_op19 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op19 (Types base) (selected base ops) = @ExternalFuns.op19 (Types base) ops := rfl
#print axioms preserved_op19
theorem preserved_op20 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op20 (Types base) (selected base ops) = @ExternalFuns.op20 (Types base) ops := rfl
#print axioms preserved_op20
theorem preserved_op21 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op21 (Types base) (selected base ops) = @ExternalFuns.op21 (Types base) ops := rfl
#print axioms preserved_op21
theorem preserved_op22 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op22 (Types base) (selected base ops) = @ExternalFuns.op22 (Types base) ops := rfl
#print axioms preserved_op22
theorem preserved_op23 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op23 (Types base) (selected base ops) = @ExternalFuns.op23 (Types base) ops := rfl
#print axioms preserved_op23
theorem preserved_op24 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op24 (Types base) (selected base ops) = @ExternalFuns.op24 (Types base) ops := rfl
#print axioms preserved_op24
theorem preserved_op25 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op25 (Types base) (selected base ops) = @ExternalFuns.op25 (Types base) ops := rfl
#print axioms preserved_op25
theorem preserved_op26 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op26 (Types base) (selected base ops) = @ExternalFuns.op26 (Types base) ops := rfl
#print axioms preserved_op26
theorem preserved_op27 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op27 (Types base) (selected base ops) = @ExternalFuns.op27 (Types base) ops := rfl
#print axioms preserved_op27
theorem preserved_op28 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op28 (Types base) (selected base ops) = @ExternalFuns.op28 (Types base) ops := rfl
#print axioms preserved_op28
theorem preserved_op29 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op29 (Types base) (selected base ops) = @ExternalFuns.op29 (Types base) ops := rfl
#print axioms preserved_op29
theorem preserved_op30 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op30 (Types base) (selected base ops) = @ExternalFuns.op30 (Types base) ops := rfl
#print axioms preserved_op30
theorem preserved_op31 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op31 (Types base) (selected base ops) = @ExternalFuns.op31 (Types base) ops := rfl
#print axioms preserved_op31
theorem preserved_op32 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op32 (Types base) (selected base ops) = @ExternalFuns.op32 (Types base) ops := rfl
#print axioms preserved_op32
theorem preserved_op33 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op33 (Types base) (selected base ops) = @ExternalFuns.op33 (Types base) ops := rfl
#print axioms preserved_op33
theorem preserved_op34 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op34 (Types base) (selected base ops) = @ExternalFuns.op34 (Types base) ops := rfl
#print axioms preserved_op34
theorem preserved_op35 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op35 (Types base) (selected base ops) = @ExternalFuns.op35 (Types base) ops := rfl
#print axioms preserved_op35
theorem preserved_op36 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op36 (Types base) (selected base ops) = @ExternalFuns.op36 (Types base) ops := rfl
#print axioms preserved_op36
theorem preserved_op37 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op37 (Types base) (selected base ops) = @ExternalFuns.op37 (Types base) ops := rfl
#print axioms preserved_op37
theorem preserved_op38 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op38 (Types base) (selected base ops) = @ExternalFuns.op38 (Types base) ops := rfl
#print axioms preserved_op38
theorem preserved_op39 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op39 (Types base) (selected base ops) = @ExternalFuns.op39 (Types base) ops := rfl
#print axioms preserved_op39
theorem preserved_op40 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op40 (Types base) (selected base ops) = @ExternalFuns.op40 (Types base) ops := rfl
#print axioms preserved_op40
theorem preserved_op41 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op41 (Types base) (selected base ops) = @ExternalFuns.op41 (Types base) ops := rfl
#print axioms preserved_op41
theorem preserved_op42 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op42 (Types base) (selected base ops) = @ExternalFuns.op42 (Types base) ops := rfl
#print axioms preserved_op42
theorem preserved_op43 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op43 (Types base) (selected base ops) = @ExternalFuns.op43 (Types base) ops := rfl
#print axioms preserved_op43
theorem preserved_op44 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op44 (Types base) (selected base ops) = @ExternalFuns.op44 (Types base) ops := rfl
#print axioms preserved_op44
theorem preserved_op45 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op45 (Types base) (selected base ops) = @ExternalFuns.op45 (Types base) ops := rfl
#print axioms preserved_op45
theorem preserved_op46 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op46 (Types base) (selected base ops) = @ExternalFuns.op46 (Types base) ops := rfl
#print axioms preserved_op46
theorem preserved_op47 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op47 (Types base) (selected base ops) = @ExternalFuns.op47 (Types base) ops := rfl
#print axioms preserved_op47
theorem preserved_op48 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op48 (Types base) (selected base ops) = @ExternalFuns.op48 (Types base) ops := rfl
#print axioms preserved_op48
theorem preserved_op49 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op49 (Types base) (selected base ops) = @ExternalFuns.op49 (Types base) ops := rfl
#print axioms preserved_op49
theorem preserved_op50 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op50 (Types base) (selected base ops) = @ExternalFuns.op50 (Types base) ops := rfl
#print axioms preserved_op50
theorem preserved_op51 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op51 (Types base) (selected base ops) = @ExternalFuns.op51 (Types base) ops := rfl
#print axioms preserved_op51
theorem preserved_op52 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op52 (Types base) (selected base ops) = @ExternalFuns.op52 (Types base) ops := rfl
#print axioms preserved_op52
theorem preserved_op53 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op53 (Types base) (selected base ops) = @ExternalFuns.op53 (Types base) ops := rfl
#print axioms preserved_op53
theorem preserved_op54 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op54 (Types base) (selected base ops) = @ExternalFuns.op54 (Types base) ops := rfl
#print axioms preserved_op54
theorem preserved_op55 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op55 (Types base) (selected base ops) = @ExternalFuns.op55 (Types base) ops := rfl
#print axioms preserved_op55
theorem preserved_op56 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op56 (Types base) (selected base ops) = @ExternalFuns.op56 (Types base) ops := rfl
#print axioms preserved_op56
theorem preserved_op57 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op57 (Types base) (selected base ops) = @ExternalFuns.op57 (Types base) ops := rfl
#print axioms preserved_op57
theorem preserved_op58 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op58 (Types base) (selected base ops) = @ExternalFuns.op58 (Types base) ops := rfl
#print axioms preserved_op58
theorem preserved_op59 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op59 (Types base) (selected base ops) = @ExternalFuns.op59 (Types base) ops := rfl
#print axioms preserved_op59
theorem preserved_op60 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op60 (Types base) (selected base ops) = @ExternalFuns.op60 (Types base) ops := rfl
#print axioms preserved_op60
theorem preserved_op61 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op61 (Types base) (selected base ops) = @ExternalFuns.op61 (Types base) ops := rfl
#print axioms preserved_op61
theorem preserved_op62 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op62 (Types base) (selected base ops) = @ExternalFuns.op62 (Types base) ops := rfl
#print axioms preserved_op62
theorem preserved_op63 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op63 (Types base) (selected base ops) = @ExternalFuns.op63 (Types base) ops := rfl
#print axioms preserved_op63
theorem preserved_op64 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op64 (Types base) (selected base ops) = @ExternalFuns.op64 (Types base) ops := rfl
#print axioms preserved_op64
theorem preserved_op65 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op65 (Types base) (selected base ops) = @ExternalFuns.op65 (Types base) ops := rfl
#print axioms preserved_op65
theorem preserved_op66 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op66 (Types base) (selected base ops) = @ExternalFuns.op66 (Types base) ops := rfl
#print axioms preserved_op66
theorem preserved_op67 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op67 (Types base) (selected base ops) = @ExternalFuns.op67 (Types base) ops := rfl
#print axioms preserved_op67
theorem preserved_op68 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op68 (Types base) (selected base ops) = @ExternalFuns.op68 (Types base) ops := rfl
#print axioms preserved_op68
theorem preserved_op69 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op69 (Types base) (selected base ops) = @ExternalFuns.op69 (Types base) ops := rfl
#print axioms preserved_op69
theorem preserved_op70 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op70 (Types base) (selected base ops) = @ExternalFuns.op70 (Types base) ops := rfl
#print axioms preserved_op70
theorem preserved_op71 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op71 (Types base) (selected base ops) = @ExternalFuns.op71 (Types base) ops := rfl
#print axioms preserved_op71
theorem preserved_op72 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op72 (Types base) (selected base ops) = @ExternalFuns.op72 (Types base) ops := rfl
#print axioms preserved_op72
theorem preserved_op73 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op73 (Types base) (selected base ops) = @ExternalFuns.op73 (Types base) ops := rfl
#print axioms preserved_op73
theorem preserved_op74 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op74 (Types base) (selected base ops) = @ExternalFuns.op74 (Types base) ops := rfl
#print axioms preserved_op74
theorem preserved_op75 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op75 (Types base) (selected base ops) = @ExternalFuns.op75 (Types base) ops := rfl
#print axioms preserved_op75
theorem preserved_op76 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op76 (Types base) (selected base ops) = @ExternalFuns.op76 (Types base) ops := rfl
#print axioms preserved_op76
theorem preserved_op77 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op77 (Types base) (selected base ops) = @ExternalFuns.op77 (Types base) ops := rfl
#print axioms preserved_op77
theorem preserved_op78 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op78 (Types base) (selected base ops) = @ExternalFuns.op78 (Types base) ops := rfl
#print axioms preserved_op78
theorem preserved_op79 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op79 (Types base) (selected base ops) = @ExternalFuns.op79 (Types base) ops := rfl
#print axioms preserved_op79
theorem preserved_op80 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op80 (Types base) (selected base ops) = @ExternalFuns.op80 (Types base) ops := rfl
#print axioms preserved_op80
theorem preserved_op81 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op81 (Types base) (selected base ops) = @ExternalFuns.op81 (Types base) ops := rfl
#print axioms preserved_op81
theorem preserved_op82 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op82 (Types base) (selected base ops) = @ExternalFuns.op82 (Types base) ops := rfl
#print axioms preserved_op82
theorem preserved_op83 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op83 (Types base) (selected base ops) = @ExternalFuns.op83 (Types base) ops := rfl
#print axioms preserved_op83
theorem preserved_op84 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op84 (Types base) (selected base ops) = @ExternalFuns.op84 (Types base) ops := rfl
#print axioms preserved_op84
theorem preserved_op85 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op85 (Types base) (selected base ops) = @ExternalFuns.op85 (Types base) ops := rfl
#print axioms preserved_op85
theorem preserved_op86 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op86 (Types base) (selected base ops) = @ExternalFuns.op86 (Types base) ops := rfl
#print axioms preserved_op86
theorem preserved_op87 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op87 (Types base) (selected base ops) = @ExternalFuns.op87 (Types base) ops := rfl
#print axioms preserved_op87
theorem preserved_op88 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op88 (Types base) (selected base ops) = @ExternalFuns.op88 (Types base) ops := rfl
#print axioms preserved_op88
theorem preserved_op89 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op89 (Types base) (selected base ops) = @ExternalFuns.op89 (Types base) ops := rfl
#print axioms preserved_op89
theorem preserved_op90 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op90 (Types base) (selected base ops) = @ExternalFuns.op90 (Types base) ops := rfl
#print axioms preserved_op90
theorem preserved_op91 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op91 (Types base) (selected base ops) = @ExternalFuns.op91 (Types base) ops := rfl
#print axioms preserved_op91
theorem preserved_op92 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op92 (Types base) (selected base ops) = @ExternalFuns.op92 (Types base) ops := rfl
#print axioms preserved_op92
theorem preserved_op93 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op93 (Types base) (selected base ops) = @ExternalFuns.op93 (Types base) ops := rfl
#print axioms preserved_op93
theorem preserved_op94 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op94 (Types base) (selected base ops) = @ExternalFuns.op94 (Types base) ops := rfl
#print axioms preserved_op94
theorem preserved_op95 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op95 (Types base) (selected base ops) = @ExternalFuns.op95 (Types base) ops := rfl
#print axioms preserved_op95
theorem preserved_op96 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op96 (Types base) (selected base ops) = @ExternalFuns.op96 (Types base) ops := rfl
#print axioms preserved_op96
theorem preserved_op97 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op97 (Types base) (selected base ops) = @ExternalFuns.op97 (Types base) ops := rfl
#print axioms preserved_op97
theorem preserved_op98 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op98 (Types base) (selected base ops) = @ExternalFuns.op98 (Types base) ops := rfl
#print axioms preserved_op98
theorem preserved_op99 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op99 (Types base) (selected base ops) = @ExternalFuns.op99 (Types base) ops := rfl
#print axioms preserved_op99
theorem preserved_op100 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op100 (Types base) (selected base ops) = @ExternalFuns.op100 (Types base) ops := rfl
#print axioms preserved_op100
theorem preserved_op101 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op101 (Types base) (selected base ops) = @ExternalFuns.op101 (Types base) ops := rfl
#print axioms preserved_op101
theorem preserved_op102 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op102 (Types base) (selected base ops) = @ExternalFuns.op102 (Types base) ops := rfl
#print axioms preserved_op102
theorem preserved_op103 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op103 (Types base) (selected base ops) = @ExternalFuns.op103 (Types base) ops := rfl
#print axioms preserved_op103
theorem preserved_op104 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op104 (Types base) (selected base ops) = @ExternalFuns.op104 (Types base) ops := rfl
#print axioms preserved_op104
theorem preserved_op105 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op105 (Types base) (selected base ops) = @ExternalFuns.op105 (Types base) ops := rfl
#print axioms preserved_op105
theorem preserved_op106 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op106 (Types base) (selected base ops) = @ExternalFuns.op106 (Types base) ops := rfl
#print axioms preserved_op106
theorem preserved_op107 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op107 (Types base) (selected base ops) = @ExternalFuns.op107 (Types base) ops := rfl
#print axioms preserved_op107
theorem preserved_op108 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op108 (Types base) (selected base ops) = @ExternalFuns.op108 (Types base) ops := rfl
#print axioms preserved_op108
theorem preserved_op109 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op109 (Types base) (selected base ops) = @ExternalFuns.op109 (Types base) ops := rfl
#print axioms preserved_op109
theorem preserved_op110 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op110 (Types base) (selected base ops) = @ExternalFuns.op110 (Types base) ops := rfl
#print axioms preserved_op110
theorem preserved_op111 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op111 (Types base) (selected base ops) = @ExternalFuns.op111 (Types base) ops := rfl
#print axioms preserved_op111
theorem preserved_op112 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op112 (Types base) (selected base ops) = @ExternalFuns.op112 (Types base) ops := rfl
#print axioms preserved_op112
theorem preserved_op113 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op113 (Types base) (selected base ops) = @ExternalFuns.op113 (Types base) ops := rfl
#print axioms preserved_op113
theorem preserved_op114 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op114 (Types base) (selected base ops) = @ExternalFuns.op114 (Types base) ops := rfl
#print axioms preserved_op114
theorem preserved_op115 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op115 (Types base) (selected base ops) = @ExternalFuns.op115 (Types base) ops := rfl
#print axioms preserved_op115
theorem preserved_op116 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op116 (Types base) (selected base ops) = @ExternalFuns.op116 (Types base) ops := rfl
#print axioms preserved_op116
theorem preserved_op117 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op117 (Types base) (selected base ops) = @ExternalFuns.op117 (Types base) ops := rfl
#print axioms preserved_op117
theorem preserved_op118 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op118 (Types base) (selected base ops) = @ExternalFuns.op118 (Types base) ops := rfl
#print axioms preserved_op118
theorem preserved_op119 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op119 (Types base) (selected base ops) = @ExternalFuns.op119 (Types base) ops := rfl
#print axioms preserved_op119
theorem preserved_op120 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op120 (Types base) (selected base ops) = @ExternalFuns.op120 (Types base) ops := rfl
#print axioms preserved_op120
theorem preserved_op121 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op121 (Types base) (selected base ops) = @ExternalFuns.op121 (Types base) ops := rfl
#print axioms preserved_op121
theorem preserved_op122 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op122 (Types base) (selected base ops) = @ExternalFuns.op122 (Types base) ops := rfl
#print axioms preserved_op122
theorem preserved_op123 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op123 (Types base) (selected base ops) = @ExternalFuns.op123 (Types base) ops := rfl
#print axioms preserved_op123
theorem preserved_op124 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op124 (Types base) (selected base ops) = @ExternalFuns.op124 (Types base) ops := rfl
#print axioms preserved_op124
theorem preserved_op125 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op125 (Types base) (selected base ops) = @ExternalFuns.op125 (Types base) ops := rfl
#print axioms preserved_op125
theorem preserved_op126 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op126 (Types base) (selected base ops) = @ExternalFuns.op126 (Types base) ops := rfl
#print axioms preserved_op126
theorem preserved_op127 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op127 (Types base) (selected base ops) = @ExternalFuns.op127 (Types base) ops := rfl
#print axioms preserved_op127
theorem preserved_op128 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op128 (Types base) (selected base ops) = @ExternalFuns.op128 (Types base) ops := rfl
#print axioms preserved_op128
theorem preserved_op129 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op129 (Types base) (selected base ops) = @ExternalFuns.op129 (Types base) ops := rfl
#print axioms preserved_op129
theorem preserved_op130 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op130 (Types base) (selected base ops) = @ExternalFuns.op130 (Types base) ops := rfl
#print axioms preserved_op130
theorem preserved_op131 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op131 (Types base) (selected base ops) = @ExternalFuns.op131 (Types base) ops := rfl
#print axioms preserved_op131
theorem preserved_op132 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op132 (Types base) (selected base ops) = @ExternalFuns.op132 (Types base) ops := rfl
#print axioms preserved_op132
theorem preserved_op133 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op133 (Types base) (selected base ops) = @ExternalFuns.op133 (Types base) ops := rfl
#print axioms preserved_op133
theorem preserved_op134 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op134 (Types base) (selected base ops) = @ExternalFuns.op134 (Types base) ops := rfl
#print axioms preserved_op134
theorem preserved_op135 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op135 (Types base) (selected base ops) = @ExternalFuns.op135 (Types base) ops := rfl
#print axioms preserved_op135
theorem preserved_op136 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op136 (Types base) (selected base ops) = @ExternalFuns.op136 (Types base) ops := rfl
#print axioms preserved_op136
theorem preserved_op137 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op137 (Types base) (selected base ops) = @ExternalFuns.op137 (Types base) ops := rfl
#print axioms preserved_op137
theorem preserved_op138 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op138 (Types base) (selected base ops) = @ExternalFuns.op138 (Types base) ops := rfl
#print axioms preserved_op138
theorem preserved_op139 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op139 (Types base) (selected base ops) = @ExternalFuns.op139 (Types base) ops := rfl
#print axioms preserved_op139
theorem preserved_op140 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op140 (Types base) (selected base ops) = @ExternalFuns.op140 (Types base) ops := rfl
#print axioms preserved_op140
theorem preserved_op141 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op141 (Types base) (selected base ops) = @ExternalFuns.op141 (Types base) ops := rfl
#print axioms preserved_op141
theorem preserved_op142 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op142 (Types base) (selected base ops) = @ExternalFuns.op142 (Types base) ops := rfl
#print axioms preserved_op142
theorem preserved_op143 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op143 (Types base) (selected base ops) = @ExternalFuns.op143 (Types base) ops := rfl
#print axioms preserved_op143
theorem preserved_op144 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op144 (Types base) (selected base ops) = @ExternalFuns.op144 (Types base) ops := rfl
#print axioms preserved_op144
theorem preserved_op145 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op145 (Types base) (selected base ops) = @ExternalFuns.op145 (Types base) ops := rfl
#print axioms preserved_op145
theorem preserved_op146 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op146 (Types base) (selected base ops) = @ExternalFuns.op146 (Types base) ops := rfl
#print axioms preserved_op146
theorem preserved_op147 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op147 (Types base) (selected base ops) = @ExternalFuns.op147 (Types base) ops := rfl
#print axioms preserved_op147
theorem preserved_op148 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op148 (Types base) (selected base ops) = @ExternalFuns.op148 (Types base) ops := rfl
#print axioms preserved_op148
theorem preserved_op149 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op149 (Types base) (selected base ops) = @ExternalFuns.op149 (Types base) ops := rfl
#print axioms preserved_op149
theorem preserved_op150 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op150 (Types base) (selected base ops) = @ExternalFuns.op150 (Types base) ops := rfl
#print axioms preserved_op150
theorem preserved_op151 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op151 (Types base) (selected base ops) = @ExternalFuns.op151 (Types base) ops := rfl
#print axioms preserved_op151
theorem preserved_op152 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op152 (Types base) (selected base ops) = @ExternalFuns.op152 (Types base) ops := rfl
#print axioms preserved_op152
theorem preserved_op153 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op153 (Types base) (selected base ops) = @ExternalFuns.op153 (Types base) ops := rfl
#print axioms preserved_op153
theorem preserved_op154 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op154 (Types base) (selected base ops) = @ExternalFuns.op154 (Types base) ops := rfl
#print axioms preserved_op154
theorem preserved_op155 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op155 (Types base) (selected base ops) = @ExternalFuns.op155 (Types base) ops := rfl
#print axioms preserved_op155
theorem preserved_op156 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op156 (Types base) (selected base ops) = @ExternalFuns.op156 (Types base) ops := rfl
#print axioms preserved_op156
theorem preserved_op157 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op157 (Types base) (selected base ops) = @ExternalFuns.op157 (Types base) ops := rfl
#print axioms preserved_op157
theorem preserved_op158 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op158 (Types base) (selected base ops) = @ExternalFuns.op158 (Types base) ops := rfl
#print axioms preserved_op158
theorem preserved_op159 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op159 (Types base) (selected base ops) = @ExternalFuns.op159 (Types base) ops := rfl
#print axioms preserved_op159
theorem preserved_op160 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op160 (Types base) (selected base ops) = @ExternalFuns.op160 (Types base) ops := rfl
#print axioms preserved_op160
theorem preserved_op161 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op161 (Types base) (selected base ops) = @ExternalFuns.op161 (Types base) ops := rfl
#print axioms preserved_op161
theorem preserved_op162 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op162 (Types base) (selected base ops) = @ExternalFuns.op162 (Types base) ops := rfl
#print axioms preserved_op162
theorem preserved_op163 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op163 (Types base) (selected base ops) = @ExternalFuns.op163 (Types base) ops := rfl
#print axioms preserved_op163
theorem preserved_op164 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op164 (Types base) (selected base ops) = @ExternalFuns.op164 (Types base) ops := rfl
#print axioms preserved_op164
theorem preserved_op165 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op165 (Types base) (selected base ops) = @ExternalFuns.op165 (Types base) ops := rfl
#print axioms preserved_op165
theorem preserved_op166 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op166 (Types base) (selected base ops) = @ExternalFuns.op166 (Types base) ops := rfl
#print axioms preserved_op166
theorem preserved_op167 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op167 (Types base) (selected base ops) = @ExternalFuns.op167 (Types base) ops := rfl
#print axioms preserved_op167
theorem preserved_op168 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op168 (Types base) (selected base ops) = @ExternalFuns.op168 (Types base) ops := rfl
#print axioms preserved_op168
theorem preserved_op169 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op169 (Types base) (selected base ops) = @ExternalFuns.op169 (Types base) ops := rfl
#print axioms preserved_op169
theorem preserved_op170 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op170 (Types base) (selected base ops) = @ExternalFuns.op170 (Types base) ops := rfl
#print axioms preserved_op170
theorem preserved_op171 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op171 (Types base) (selected base ops) = @ExternalFuns.op171 (Types base) ops := rfl
#print axioms preserved_op171
theorem preserved_op172 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op172 (Types base) (selected base ops) = @ExternalFuns.op172 (Types base) ops := rfl
#print axioms preserved_op172
theorem preserved_op173 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op173 (Types base) (selected base ops) = @ExternalFuns.op173 (Types base) ops := rfl
#print axioms preserved_op173
theorem preserved_op174 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op174 (Types base) (selected base ops) = @ExternalFuns.op174 (Types base) ops := rfl
#print axioms preserved_op174
theorem preserved_op175 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op175 (Types base) (selected base ops) = @ExternalFuns.op175 (Types base) ops := rfl
#print axioms preserved_op175
theorem preserved_op176 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op176 (Types base) (selected base ops) = @ExternalFuns.op176 (Types base) ops := rfl
#print axioms preserved_op176
theorem preserved_op177 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op177 (Types base) (selected base ops) = @ExternalFuns.op177 (Types base) ops := rfl
#print axioms preserved_op177
theorem preserved_op178 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op178 (Types base) (selected base ops) = @ExternalFuns.op178 (Types base) ops := rfl
#print axioms preserved_op178
theorem preserved_op179 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op179 (Types base) (selected base ops) = @ExternalFuns.op179 (Types base) ops := rfl
#print axioms preserved_op179
theorem preserved_op180 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op180 (Types base) (selected base ops) = @ExternalFuns.op180 (Types base) ops := rfl
#print axioms preserved_op180
theorem preserved_op181 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op181 (Types base) (selected base ops) = @ExternalFuns.op181 (Types base) ops := rfl
#print axioms preserved_op181
theorem preserved_op182 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op182 (Types base) (selected base ops) = @ExternalFuns.op182 (Types base) ops := rfl
#print axioms preserved_op182
theorem preserved_op183 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op183 (Types base) (selected base ops) = @ExternalFuns.op183 (Types base) ops := rfl
#print axioms preserved_op183
theorem preserved_op184 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op184 (Types base) (selected base ops) = @ExternalFuns.op184 (Types base) ops := rfl
#print axioms preserved_op184
theorem preserved_op185 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op185 (Types base) (selected base ops) = @ExternalFuns.op185 (Types base) ops := rfl
#print axioms preserved_op185
theorem preserved_op186 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op186 (Types base) (selected base ops) = @ExternalFuns.op186 (Types base) ops := rfl
#print axioms preserved_op186
theorem preserved_op187 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op187 (Types base) (selected base ops) = @ExternalFuns.op187 (Types base) ops := rfl
#print axioms preserved_op187
theorem preserved_op188 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op188 (Types base) (selected base ops) = @ExternalFuns.op188 (Types base) ops := rfl
#print axioms preserved_op188
theorem preserved_op189 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op189 (Types base) (selected base ops) = @ExternalFuns.op189 (Types base) ops := rfl
#print axioms preserved_op189
theorem preserved_op190 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op190 (Types base) (selected base ops) = @ExternalFuns.op190 (Types base) ops := rfl
#print axioms preserved_op190
theorem preserved_op191 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op191 (Types base) (selected base ops) = @ExternalFuns.op191 (Types base) ops := rfl
#print axioms preserved_op191
theorem preserved_op192 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op192 (Types base) (selected base ops) = @ExternalFuns.op192 (Types base) ops := rfl
#print axioms preserved_op192
theorem preserved_op193 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op193 (Types base) (selected base ops) = @ExternalFuns.op193 (Types base) ops := rfl
#print axioms preserved_op193
theorem preserved_op194 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op194 (Types base) (selected base ops) = @ExternalFuns.op194 (Types base) ops := rfl
#print axioms preserved_op194
theorem preserved_op195 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op195 (Types base) (selected base ops) = @ExternalFuns.op195 (Types base) ops := rfl
#print axioms preserved_op195
theorem preserved_op196 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op196 (Types base) (selected base ops) = @ExternalFuns.op196 (Types base) ops := rfl
#print axioms preserved_op196
theorem preserved_op197 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op197 (Types base) (selected base ops) = @ExternalFuns.op197 (Types base) ops := rfl
#print axioms preserved_op197
theorem preserved_op198 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op198 (Types base) (selected base ops) = @ExternalFuns.op198 (Types base) ops := rfl
#print axioms preserved_op198
theorem preserved_op199 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op199 (Types base) (selected base ops) = @ExternalFuns.op199 (Types base) ops := rfl
#print axioms preserved_op199
theorem preserved_op200 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op200 (Types base) (selected base ops) = @ExternalFuns.op200 (Types base) ops := rfl
#print axioms preserved_op200
theorem preserved_op201 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op201 (Types base) (selected base ops) = @ExternalFuns.op201 (Types base) ops := rfl
#print axioms preserved_op201
theorem preserved_op202 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op202 (Types base) (selected base ops) = @ExternalFuns.op202 (Types base) ops := rfl
#print axioms preserved_op202
theorem preserved_op203 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op203 (Types base) (selected base ops) = @ExternalFuns.op203 (Types base) ops := rfl
#print axioms preserved_op203
theorem preserved_op204 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op204 (Types base) (selected base ops) = @ExternalFuns.op204 (Types base) ops := rfl
#print axioms preserved_op204
theorem preserved_op205 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op205 (Types base) (selected base ops) = @ExternalFuns.op205 (Types base) ops := rfl
#print axioms preserved_op205
theorem preserved_op206 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op206 (Types base) (selected base ops) = @ExternalFuns.op206 (Types base) ops := rfl
#print axioms preserved_op206
theorem preserved_op207 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op207 (Types base) (selected base ops) = @ExternalFuns.op207 (Types base) ops := rfl
#print axioms preserved_op207
theorem preserved_op208 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op208 (Types base) (selected base ops) = @ExternalFuns.op208 (Types base) ops := rfl
#print axioms preserved_op208
theorem preserved_op209 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op209 (Types base) (selected base ops) = @ExternalFuns.op209 (Types base) ops := rfl
#print axioms preserved_op209
theorem preserved_op210 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op210 (Types base) (selected base ops) = @ExternalFuns.op210 (Types base) ops := rfl
#print axioms preserved_op210
theorem preserved_op211 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op211 (Types base) (selected base ops) = @ExternalFuns.op211 (Types base) ops := rfl
#print axioms preserved_op211
theorem preserved_op212 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op212 (Types base) (selected base ops) = @ExternalFuns.op212 (Types base) ops := rfl
#print axioms preserved_op212
theorem preserved_op213 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op213 (Types base) (selected base ops) = @ExternalFuns.op213 (Types base) ops := rfl
#print axioms preserved_op213
theorem preserved_op214 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op214 (Types base) (selected base ops) = @ExternalFuns.op214 (Types base) ops := rfl
#print axioms preserved_op214
theorem preserved_op215 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op215 (Types base) (selected base ops) = @ExternalFuns.op215 (Types base) ops := rfl
#print axioms preserved_op215
theorem preserved_op216 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op216 (Types base) (selected base ops) = @ExternalFuns.op216 (Types base) ops := rfl
#print axioms preserved_op216
theorem preserved_op217 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op217 (Types base) (selected base ops) = @ExternalFuns.op217 (Types base) ops := rfl
#print axioms preserved_op217
theorem preserved_op218 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op218 (Types base) (selected base ops) = @ExternalFuns.op218 (Types base) ops := rfl
#print axioms preserved_op218
theorem preserved_op219 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op219 (Types base) (selected base ops) = @ExternalFuns.op219 (Types base) ops := rfl
#print axioms preserved_op219
theorem preserved_op220 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op220 (Types base) (selected base ops) = @ExternalFuns.op220 (Types base) ops := rfl
#print axioms preserved_op220
theorem preserved_op221 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op221 (Types base) (selected base ops) = @ExternalFuns.op221 (Types base) ops := rfl
#print axioms preserved_op221
theorem preserved_op222 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op222 (Types base) (selected base ops) = @ExternalFuns.op222 (Types base) ops := rfl
#print axioms preserved_op222
theorem preserved_op223 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op223 (Types base) (selected base ops) = @ExternalFuns.op223 (Types base) ops := rfl
#print axioms preserved_op223
theorem preserved_op224 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op224 (Types base) (selected base ops) = @ExternalFuns.op224 (Types base) ops := rfl
#print axioms preserved_op224
theorem preserved_op225 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op225 (Types base) (selected base ops) = @ExternalFuns.op225 (Types base) ops := rfl
#print axioms preserved_op225
theorem preserved_op227 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op227 (Types base) (selected base ops) = @ExternalFuns.op227 (Types base) ops := rfl
#print axioms preserved_op227
theorem preserved_op228 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op228 (Types base) (selected base ops) = @ExternalFuns.op228 (Types base) ops := rfl
#print axioms preserved_op228
theorem preserved_op229 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op229 (Types base) (selected base ops) = @ExternalFuns.op229 (Types base) ops := rfl
#print axioms preserved_op229
theorem preserved_op230 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op230 (Types base) (selected base ops) = @ExternalFuns.op230 (Types base) ops := rfl
#print axioms preserved_op230
theorem preserved_op231 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op231 (Types base) (selected base ops) = @ExternalFuns.op231 (Types base) ops := rfl
#print axioms preserved_op231
theorem preserved_op232 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op232 (Types base) (selected base ops) = @ExternalFuns.op232 (Types base) ops := rfl
#print axioms preserved_op232
theorem preserved_op233 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op233 (Types base) (selected base ops) = @ExternalFuns.op233 (Types base) ops := rfl
#print axioms preserved_op233
theorem preserved_op234 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op234 (Types base) (selected base ops) = @ExternalFuns.op234 (Types base) ops := rfl
#print axioms preserved_op234
theorem preserved_op235 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op235 (Types base) (selected base ops) = @ExternalFuns.op235 (Types base) ops := rfl
#print axioms preserved_op235
theorem preserved_op236 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op236 (Types base) (selected base ops) = @ExternalFuns.op236 (Types base) ops := rfl
#print axioms preserved_op236
theorem preserved_op237 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op237 (Types base) (selected base ops) = @ExternalFuns.op237 (Types base) ops := rfl
#print axioms preserved_op237
theorem preserved_op238 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op238 (Types base) (selected base ops) = @ExternalFuns.op238 (Types base) ops := rfl
#print axioms preserved_op238
theorem preserved_op239 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op239 (Types base) (selected base ops) = @ExternalFuns.op239 (Types base) ops := rfl
#print axioms preserved_op239
theorem preserved_op240 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op240 (Types base) (selected base ops) = @ExternalFuns.op240 (Types base) ops := rfl
#print axioms preserved_op240
theorem preserved_op241 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op241 (Types base) (selected base ops) = @ExternalFuns.op241 (Types base) ops := rfl
#print axioms preserved_op241
theorem preserved_op242 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op242 (Types base) (selected base ops) = @ExternalFuns.op242 (Types base) ops := rfl
#print axioms preserved_op242
theorem preserved_op243 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op243 (Types base) (selected base ops) = @ExternalFuns.op243 (Types base) ops := rfl
#print axioms preserved_op243
theorem preserved_op244 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op244 (Types base) (selected base ops) = @ExternalFuns.op244 (Types base) ops := rfl
#print axioms preserved_op244
theorem preserved_op245 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op245 (Types base) (selected base ops) = @ExternalFuns.op245 (Types base) ops := rfl
#print axioms preserved_op245
theorem preserved_op246 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op246 (Types base) (selected base ops) = @ExternalFuns.op246 (Types base) ops := rfl
#print axioms preserved_op246
theorem preserved_op247 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op247 (Types base) (selected base ops) = @ExternalFuns.op247 (Types base) ops := rfl
#print axioms preserved_op247
theorem preserved_op248 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op248 (Types base) (selected base ops) = @ExternalFuns.op248 (Types base) ops := rfl
#print axioms preserved_op248
theorem preserved_op249 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op249 (Types base) (selected base ops) = @ExternalFuns.op249 (Types base) ops := rfl
#print axioms preserved_op249
theorem preserved_op250 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op250 (Types base) (selected base ops) = @ExternalFuns.op250 (Types base) ops := rfl
#print axioms preserved_op250
theorem preserved_op251 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op251 (Types base) (selected base ops) = @ExternalFuns.op251 (Types base) ops := rfl
#print axioms preserved_op251
theorem preserved_op252 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op252 (Types base) (selected base ops) = @ExternalFuns.op252 (Types base) ops := rfl
#print axioms preserved_op252
theorem preserved_op253 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op253 (Types base) (selected base ops) = @ExternalFuns.op253 (Types base) ops := rfl
#print axioms preserved_op253
theorem preserved_op254 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op254 (Types base) (selected base ops) = @ExternalFuns.op254 (Types base) ops := rfl
#print axioms preserved_op254
theorem preserved_op255 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op255 (Types base) (selected base ops) = @ExternalFuns.op255 (Types base) ops := rfl
#print axioms preserved_op255
theorem preserved_op256 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op256 (Types base) (selected base ops) = @ExternalFuns.op256 (Types base) ops := rfl
#print axioms preserved_op256
theorem preserved_op257 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op257 (Types base) (selected base ops) = @ExternalFuns.op257 (Types base) ops := rfl
#print axioms preserved_op257
theorem preserved_op258 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op258 (Types base) (selected base ops) = @ExternalFuns.op258 (Types base) ops := rfl
#print axioms preserved_op258
theorem preserved_op259 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op259 (Types base) (selected base ops) = @ExternalFuns.op259 (Types base) ops := rfl
#print axioms preserved_op259
theorem preserved_op260 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op260 (Types base) (selected base ops) = @ExternalFuns.op260 (Types base) ops := rfl
#print axioms preserved_op260
theorem preserved_op261 (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op261 (Types base) (selected base ops) = @ExternalFuns.op261 (Types base) ops := rfl
#print axioms preserved_op261
end
end PV_B3P_Install226V3
