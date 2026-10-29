import R1Z.PV_OWNJ_Rows
set_option autoImplicit false
namespace R1Z.PV_OWNJ_Points
open PV_OWNI_RawOps
/-- Reverse-coordinate source loop, carrying the actual ordered raw product. -/
def successorRev : List Q → Q → List Q
 | [], _ => []
 | bit::rest, carry =>
  let product := valueMul bit carry
  valueSub (valueAdd bit carry) (valueAdd product product) :: successorRev rest product

def successor (point : List Q) : List Q := (successorRev point.reverse one).reverse

def xor12 (point : List Q) : List Q :=
 point.zipIdx.map fun (x,i) => if i = 6 ∨ i = 7 then valueSub one x else x

/-- wire::statement_points returns these three points in this order. -/
def statement_points (point : List Q) : List (List Q) := [point,successor point,xor12 point]

theorem successorRev_length (point : List Q) (carry : Q) :
 (successorRev point carry).length = point.length := by
 induction point generalizing carry with
 | nil => rfl
 | cons x xs ih => simp only [successorRev,List.length_cons,ih]

theorem point_lengths (point : List Q) (p : List Q) (hp : p ∈ statement_points point) :
 p.length = point.length := by
 simp only [statement_points,List.mem_cons,List.mem_singleton] at hp
 rcases hp with rfl | rfl | rfl
 · rfl
 · simp only [successor,List.length_reverse,successorRev_length]
 · simp only [xor12,List.length_map,List.length_zipIdx]

/-- Each public transformation is independent of all column values. -/
theorem same_points (left right : List Q) (h : left = right) :
 statement_points left = statement_points right := congrArg statement_points h

#print axioms successorRev_length
#print axioms point_lengths
#print axioms same_points
end R1Z.PV_OWNJ_Points
