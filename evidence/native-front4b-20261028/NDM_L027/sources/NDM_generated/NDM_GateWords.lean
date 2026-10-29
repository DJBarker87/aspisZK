import NDM_GateRef.Funs
set_option autoImplicit false
namespace NDM_GateWords
open Aeneas Aeneas.Std Result
 theorem byte_value (x : U8) : (UScalar.cast .U64 x).val=x.val := by
 rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt (by scalar_tac)]
 theorem field_value (x : U32) : (UScalar.cast .U64 x).val=x.val := by
 rw [UScalar.cast_val_eq, Nat.mod_eq_of_lt (by scalar_tac)]
 theorem byte_injective (x y : U8) (h : UScalar.cast .U64 x=UScalar.cast .U64 y) : x=y := by
 apply UScalar.eq_of_val_eq
 have v := congrArg (fun (z : U64)=>z.val) h
 simpa only [byte_value] using v
 theorem field_injective (x y : U32) (h : UScalar.cast .U64 x=UScalar.cast .U64 y) : x=y := by
 apply UScalar.eq_of_val_eq
 have v := congrArg (fun (z : U64)=>z.val) h
 simpa only [field_value] using v
#print axioms byte_value
#print axioms field_value
#print axioms byte_injective
#print axioms field_injective
#print Aeneas.Std.U64.checked_add
end NDM_GateWords
