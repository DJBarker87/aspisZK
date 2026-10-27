import XSe_BasisUpdate
import XRu_NewStep
open Aeneas Aeneas.Std Result XRn_Join_Release
set_option autoImplicit false
namespace XSe_InitialRowPhase
abbrev Row := Array U64 4#usize
def SmallRow (row : Row) : Prop := ∀ x∈row.val,x.val<2^34
def Small (raw : XRu_NewStep.Raw) : Prop := ∀ row∈raw.val,SmallRow row
/-- Widening an arbitrary U32 is already inside the initial periodic phase. -/
theorem scalar (x : U32) : (UScalar.cast .U64 x).val<2^34 := by scalar_tac
/-- The actual four casted lanes, with no canonicality hypothesis. -/
theorem row (q : aspis_core.field.QM31) : SmallRow
 (Array.make 4#usize [UScalar.cast .U64 q.c0.a,UScalar.cast .U64 q.c0.b,
  UScalar.cast .U64 q.c1.a,UScalar.cast .U64 q.c1.b]) := by
 intro x hx
 simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at hx
 rcases hx with rfl|rfl|rfl|rfl <;> exact scalar _
/-- A source row installation preserves the initial phase envelope. -/
theorem set (raw : XRu_NewStep.Raw) (i : Usize) (q : aspis_core.field.QM31)
 (small : Small raw) : Small (raw.set i
 (Array.make 4#usize [UScalar.cast .U64 q.c0.a,UScalar.cast .U64 q.c0.b,
  UScalar.cast .U64 q.c1.a,UScalar.cast .U64 q.c1.b])) := by
 exact XSe_BasisUpdate.list SmallRow raw.val i.val _ small (row q)
#print axioms scalar
#print axioms row
#print axioms set
end XSe_InitialRowPhase
