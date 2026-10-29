import R1Z.PV_OWNJ_Claims
import R1Z.PV_OWNJ_FiatShamir
set_option autoImplicit false
namespace R1Z.PV_OWNJ_PublicInstance
open PV_OWNI_RawOps PV_OWNJ_Points PV_OWNJ_FiatShamir
open PV_RDB2D_CollectorTrace PV_RDB2D_SparseShape

def calls (point : List Q) (lengths : List Nat) : List (List Q × Nat) :=
 (statement_points point).flatMap fun p => lengths.map fun n => (p,n)

/-- One global failure prior: a wrong shape or null stops all later points. -/
def plan : List (List Q × Nat) → List Bool → List Action
 | [], _ => []
 | (p,n)::rest, failures =>
  if n ≠ 1024 then [] else
  let bytes := 24 * capacity PV_OWNI_Scanner.boolean p
  if failures.headD false then [.allocate bytes 8,.abort bytes 8] else
  [.allocate bytes 8,.deallocate bytes 8] ++ plan rest failures.tail

theorem one_point (point : List Q) (lengths : List Nat) (failures : List Bool) :
 plan (lengths.map fun n => (point,n)) failures =
 PV_OWNI_PublicPlan.plan PV_OWNI_Scanner.boolean point lengths failures := by
 induction lengths generalizing failures with
 | nil => rfl
 | cons n ns ih =>
  simp only [List.map_cons,plan,PV_OWNI_PublicPlan.plan]
  split
  · rfl
  · split
    · rfl
    · rw [ih]

theorem first_shape_stop (point : List Q) (bad : Nat) (rest : List (List Q × Nat))
 (failures : List Bool) (h : bad ≠ 1024) : plan ((point,bad)::rest) failures = [] := by
 rw [plan,if_pos h]

/-- PublicPlan.same_public is instantiated with the computed protocol point
and the actual column-length vector, not a fresh publicity hypothesis. -/
theorem per_point_public (sampleValue : Nat → Q) (hash : Hash) (sample : Bytes → Q)
 (statementBytes c1 : Bytes) (left right : List Bytes) (hp : left = right)
 (round index assignment : Nat) (failures : List Bool) :
 PV_OWNI_PublicPlan.plan PV_OWNI_Scanner.boolean
  (query sampleValue (alpha hash sample statementBytes c1 left) round index assignment)
  (List.replicate 29 1024) failures =
 PV_OWNI_PublicPlan.plan PV_OWNI_Scanner.boolean
  (query sampleValue (alpha hash sample statementBytes c1 right) round index assignment)
  (List.replicate 29 1024) failures :=
 PV_OWNI_PublicPlan.same_public PV_OWNI_Scanner.boolean _ _
  (query_public sampleValue hash sample statementBytes c1 left right hp round index assignment)
  _ _ rfl failures

theorem final_public (hash : Hash) (sample : Bytes → Q) (statementBytes c1 : Bytes)
 (left right : List Bytes) (hp : left = right) (failures : List Bool) :
 plan (calls (alpha hash sample statementBytes c1 left) (List.replicate 29 1024)) failures =
 plan (calls (alpha hash sample statementBytes c1 right) (List.replicate 29 1024)) failures := by
 rw [PV_OWNJ_FiatShamir.final_public hash sample statementBytes c1 left right hp]

/-- All three wire points, all 29 lanes and the global failure prior. -/
theorem callback_public (sampleValue : Nat → Q) (hash : Hash) (sample : Bytes → Q)
 (statementBytes c1 : Bytes) (left right : List Bytes) (hp : left = right)
 (round index assignment : Nat) (failures : List Bool)
 (columnsL columnsR : List (List Q))
 (hl : columnsL.map List.length = List.replicate 29 1024)
 (hr : columnsR.map List.length = List.replicate 29 1024) :
 plan (calls (query sampleValue (alpha hash sample statementBytes c1 left) round index assignment)
  (columnsL.map List.length)) failures =
 plan (calls (query sampleValue (alpha hash sample statementBytes c1 right) round index assignment)
  (columnsR.map List.length)) failures := by
 rw [hl,hr,query_public sampleValue hash sample statementBytes c1 left right hp round index assignment]

#print axioms callback_public
#print axioms one_point
#print axioms first_shape_stop
#print axioms per_point_public
#print axioms final_public
end R1Z.PV_OWNJ_PublicInstance
