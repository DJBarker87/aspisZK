import PV_B3P_ClosureLinks14227
namespace PV_B3Q_Std
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Groups14227
set_option autoImplicit false
inductive Body where
 | u32_u64 | bool_u32 | u16_usize | u8_usize | result_branch | usize_unwrap_or | usize_is_some
abbrev Branch := {T E : Type} → core.result.Result T E → Result (core.ops.control_flow.ControlFlow (core.result.Result core.convert.Infallible E) T)
def Signature : Body → Type
 | .u32_u64 => U32 → Result U64
 | .bool_u32 => Bool → Result U32
 | .u16_usize => U16 → Result Usize
 | .u8_usize => U8 → Result Usize
 | .result_branch => Branch
 | .usize_unwrap_or => Option Usize → Usize → Usize
 | .usize_is_some => Option Usize → Bool
/-- The two-arm 1.94.1 source match; neither payload is dropped. -/
def source_branch : Branch := fun x => match x with
 | .Ok v => .ok (.Continue v)
 | .Err e => .ok (.Break (.Err e))
/-- Selected payload is Copy, so the unused alternative has no destructor. -/
def source_unwrap_or (x : Option Usize) (fallback : Usize) : Usize :=
 match x with | some v => v | none => fallback
def source_is_some (x : Option Usize) : Bool := match x with | some _ => true | none => false
def source_u32_u64 (x : U32) : Result U64 := .ok (UScalar.cast .U64 x)
def source_bool_u32 (x : Bool) : Result U32 := .ok (UScalar.cast .U32 (UScalar.cast_fromBool .U8 x))
def source_u16_usize (x : U16) : Result Usize := .ok (UScalar.cast .Usize x)
def source_u8_usize (x : U8) : Result Usize := .ok (UScalar.cast .Usize x)
def native : (i : Body) → Signature i
 | .u32_u64 => source_u32_u64
 | .bool_u32 => source_bool_u32
 | .u16_usize => source_u16_usize
 | .u8_usize => source_u8_usize
 | .result_branch => @source_branch
 | .usize_unwrap_or => source_unwrap_or
 | .usize_is_some => source_is_some
def model : (i : Body) → Signature i
 | .u32_u64 => fun x => .ok (UScalar.cast .U64 x)
 | .bool_u32 => fun x => .ok (if x then 1#u32 else 0#u32)
 | .u16_usize => fun x => .ok (UScalar.cast .Usize x)
 | .u8_usize => fun x => .ok (UScalar.cast .Usize x)
 | .result_branch => @core.result.Result.Insts.CoreOpsTry.branch
 | .usize_unwrap_or => core.option.Option.unwrap_or
 | .usize_is_some => core.option.Option.is_some
theorem binding_u32_u64 : native .u32_u64 = model .u32_u64 := by
  rfl
#print axioms binding_u32_u64
theorem binding_bool_u32 : native .bool_u32 = model .bool_u32 := by
  funext x
  cases x <;> rfl
#print axioms binding_bool_u32
theorem binding_u16_usize : native .u16_usize = model .u16_usize := by
  rfl
#print axioms binding_u16_usize
theorem binding_u8_usize : native .u8_usize = model .u8_usize := by
  rfl
#print axioms binding_u8_usize
theorem binding_result_branch : native .result_branch = model .result_branch := by
  rfl
#print axioms binding_result_branch
theorem binding_usize_unwrap_or : native .usize_unwrap_or = model .usize_unwrap_or := by
  rfl
#print axioms binding_usize_unwrap_or
theorem binding_usize_is_some : native .usize_is_some = model .usize_is_some := by
  funext x
  cases x <;> rfl
#print axioms binding_usize_is_some
/-- Seven concrete rows only. This is NOT the full reached-cone catalogue. -/
theorem partial_catalogue_link : PV_B3P_Link_std_dependency_closure14 Signature native model := by
 intro i
 cases i
 · exact binding_u32_u64
 · exact binding_bool_u32
 · exact binding_u16_usize
 · exact binding_u8_usize
 · exact binding_result_branch
 · exact binding_usize_unwrap_or
 · exact binding_usize_is_some
#print axioms partial_catalogue_link
end PV_B3Q_Std
