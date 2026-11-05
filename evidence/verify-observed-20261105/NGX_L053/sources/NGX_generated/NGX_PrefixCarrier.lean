import NGX_PrefixSource
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.NGX_PrefixCarrier
namespace P := AspisR1PrefixAggregateParser.r1_wire
namespace C := AspisR1PublicPreparation.r1_wire

def toCaller (p : P.Prefix) : C.Prefix := ⟨p.c1_root,p.records⟩
def toParser (p : C.Prefix) : P.Prefix := ⟨p.c1_root,p.records⟩
theorem caller_roundtrip (p : C.Prefix) : toCaller (toParser p)=p := by cases p; rfl
theorem parser_roundtrip (p : P.Prefix) : toParser (toCaller p)=p := by cases p; rfl
theorem fields (p : P.Prefix) :
 (toCaller p).c1_root=p.c1_root ∧ (toCaller p).records=p.records := ⟨rfl,rfl⟩

def error : P.Error→C.Error
 | .Allocation=>.Allocation | .RowOrder e a=>.RowOrder e a | .InvalidRow=>.InvalidRow
 | .Tag r=>.Tag r | .Length r=>.Length r | .NonCanonical r v=>.NonCanonical r v
 | .Boundary r=>.Boundary r | .Terminal=>.Terminal | .EqualCirclePoints=>.EqualCirclePoints
 | .TrailingBytes=>.TrailingBytes | .Public=>.Public

def result (m : Result (core.result.Result P.Prefix P.Error)) :
 Result (core.result.Result C.Prefix C.Error) := do
 let value←m
 ok (match value with | .Ok p=>.Ok (toCaller p) | .Err e=>.Err (error e))

theorem full_result (m : Result (core.result.Result P.Prefix P.Error)) :
 result m=match m with
 | .fail e=>.fail e | .div=>.div
 | .ok (.Err e)=>.ok (.Err (error e))
 | .ok (.Ok p)=>.ok (.Ok (toCaller p)) := by
 cases m with
 | fail e=>rfl | div=>rfl | ok r=>cases r <;> rfl

theorem producer_domain (row : Nat) (bound : row≤26) :
 NGX_PrefixGeometry.start row≤13000 ∧
 5≤NGX_PrefixGeometry.width row ∧ NGX_PrefixGeometry.width row≤3717 ∧
 NGX_PrefixGeometry.start row+NGX_PrefixGeometry.width row≤17000 := by
 have s:=NGX_PrefixGeometry.start_bound row bound
 have w:=NGX_PrefixGeometry.widths row
 omega
#print axioms caller_roundtrip
#print axioms parser_roundtrip
#print axioms fields
#print axioms full_result
#print axioms producer_domain
end AspisR1.NGX_PrefixCarrier
