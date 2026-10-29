"""Generate concrete typed source-binding instances; never call a subset exhaustive."""
from pathlib import Path
D=Path('evidence/pv-b3q-20261029/lean')
s='''import PV_B3P_ClosureLinks14227
import PV_B3P_Std194Law227
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
def native : (i : Body) → Signature i
 | .u32_u64 => std194227.from_u32_u64
 | .bool_u32 => std194227.from_bool_u32
 | .u16_usize => std194227.from_u16_usize
 | .u8_usize => std194227.from_u8_usize
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
'''
names=['u32_u64','bool_u32','u16_usize','u8_usize','result_branch','usize_unwrap_or','usize_is_some']
for n in names:
 s+=f'theorem binding_{n} : native .{n} = model .{n} := by\n'
 if n in names[:4]:s+=f'  funext x\n  exact PV_B3P_Std194Law227.{n}_result x\n'
 elif n=='result_branch':s+='  rfl\n'
 elif n=='usize_unwrap_or':s+='  rfl\n'
 else:s+='  funext x\n  cases x <;> rfl\n'
 s+=f'#print axioms binding_{n}\n'
s+='''/-- Seven concrete rows only. This is NOT the full reached-cone catalogue. -/
theorem partial_catalogue_link : PV_B3P_Link_std_dependency_closure14 Signature native model := by
 intro i
 cases i
'''
for n in names:s+=f' · exact binding_{n}\n'
s+='#print axioms partial_catalogue_link\nend PV_B3Q_Std\n';(D/'PV_B3Q_StdPartial.lean').write_text(s)
