import R1Z.PV_CBL_AppendBundle
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_CBL_Resume8SelectionAudit
open ProverRwFull PV_CBL_AppendBundle
set_option autoImplicit false
theorem allocator_retained (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op32 (Types base) (selected base ops) = @ExternalFuns.op32 (Types base) ops := rfl
theorem sha205_retained (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op205 (Types base) (selected base ops) = @ExternalFuns.op205 (Types base) ops := rfl
theorem sha208_retained (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op208 (Types base) (selected base ops) = @ExternalFuns.op208 (Types base) ops := rfl
theorem sha209_retained (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op209 (Types base) (selected base ops) = @ExternalFuns.op209 (Types base) ops := rfl
theorem sha212_retained (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op212 (Types base) (selected base ops) = @ExternalFuns.op212 (Types base) ops := rfl
theorem sha215_retained (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op215 (Types base) (selected base ops) = @ExternalFuns.op215 (Types base) ops := rfl
theorem sha216_retained (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op216 (Types base) (selected base ops) = @ExternalFuns.op216 (Types base) ops := rfl
theorem sha217_retained (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op217 (Types base) (selected base ops) = @ExternalFuns.op217 (Types base) ops := rfl
theorem sha219_retained (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns.op219 (Types base) (selected base ops) = @ExternalFuns.op219 (Types base) ops := rfl
#print axioms allocator_retained
#print axioms sha205_retained
#print axioms sha208_retained
#print axioms sha209_retained
#print axioms sha212_retained
#print axioms sha215_retained
#print axioms sha216_retained
#print axioms sha217_retained
#print axioms sha219_retained
end R1Z.PV_CBL_Resume8SelectionAudit
