import PV_B3Q_ScalarEquality
namespace PV_B3Q_CompareActual
open Aeneas Aeneas.Std PV_B3P_Groups14227
set_option autoImplicit false
inductive Body where
 | eq_u8 | ne_u8 | eq_u32 | ne_u32 | eq_u64 | ne_u64 | eq_usize | ne_usize
def Signature : Body → Type
 | .eq_u8 | .ne_u8 => U8 → U8 → Bool
 | .eq_u32 | .ne_u32 => U32 → U32 → Bool
 | .eq_u64 | .ne_u64 => U64 → U64 → Bool
 | .eq_usize | .ne_usize => Usize → Usize → Bool
def source : (body : Body) → Signature body
 | .eq_u8 => fun x y => decide (x.val = y.val)
 | .ne_u8 => fun x y => decide (x.val ≠ y.val)
 | .eq_u32 => fun x y => decide (x.val = y.val)
 | .ne_u32 => fun x y => decide (x.val ≠ y.val)
 | .eq_u64 => fun x y => decide (x.val = y.val)
 | .ne_u64 => fun x y => decide (x.val ≠ y.val)
 | .eq_usize => fun x y => decide (x.val = y.val)
 | .ne_usize => fun x y => decide (x.val ≠ y.val)
def model : (body : Body) → Signature body
 | .eq_u8 => Aeneas.Std.core.cmp.impls.PartialEqU8.eq
 | .ne_u8 => Aeneas.Std.core.cmp.impls.PartialEqU8.ne
 | .eq_u32 => Aeneas.Std.core.cmp.impls.PartialEqU32.eq
 | .ne_u32 => Aeneas.Std.core.cmp.impls.PartialEqU32.ne
 | .eq_u64 => Aeneas.Std.core.cmp.impls.PartialEqU64.eq
 | .ne_u64 => Aeneas.Std.core.cmp.impls.PartialEqU64.ne
 | .eq_usize => Aeneas.Std.core.cmp.impls.PartialEqUsize.eq
 | .ne_usize => Aeneas.Std.core.cmp.impls.PartialEqUsize.ne
theorem primitive_comparison_links : PV_B3P_Link_std_dependency_closure14 Signature source model := by
 intro body
 cases body with
 | eq_u8 =>
   funext x y
   exact Result.ok.inj (PV_B3Q_ScalarEquality.eq_binding x y)
 | ne_u8 =>
   funext x y
   exact Result.ok.inj (PV_B3Q_ScalarEquality.ne_binding x y)
 | eq_u32 =>
   funext x y
   exact Result.ok.inj (PV_B3Q_ScalarEquality.eq_binding x y)
 | ne_u32 =>
   funext x y
   exact Result.ok.inj (PV_B3Q_ScalarEquality.ne_binding x y)
 | eq_u64 =>
   funext x y
   exact Result.ok.inj (PV_B3Q_ScalarEquality.eq_binding x y)
 | ne_u64 =>
   funext x y
   exact Result.ok.inj (PV_B3Q_ScalarEquality.ne_binding x y)
 | eq_usize =>
   funext x y
   exact Result.ok.inj (PV_B3Q_ScalarEquality.eq_binding x y)
 | ne_usize =>
   funext x y
   exact Result.ok.inj (PV_B3Q_ScalarEquality.ne_binding x y)
#print axioms primitive_comparison_links
#print Aeneas.Std.WP.spec
#print Aeneas.Std.core.slice.cmp.PartialEqSlice.eq_homo_spec
end PV_B3Q_CompareActual
