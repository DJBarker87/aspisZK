import R1Z.ProverRwFullTypes
import R1Z.PV_OWN_Heap
import Mathlib.Algebra.BigOperators.Field
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNM_V239
open Aeneas Aeneas.Std Result
open scoped BigOperators
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev Bytes := List Nat

def Canon (q : Q) : Prop :=
 q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
 q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

inductive Site where | callback879 | final890
 deriving DecidableEq

/-- Public loop counters and published bytes; no column or oracle value. -/
structure Public where
 statement : Bytes
 frames : List Bytes
 round : Nat
 sample : Nat
 assignment : Nat
 deriving DecidableEq

structure Input where
 pubData : Public
 site : Site
 point : List Q
 columns : List (List Q)

inductive Action where
 | allocate (bytes align : Nat)
 | deallocate (bytes align : Nat)
 | abort (bytes align : Nat)
 deriving DecidableEq

/-- Same first-shape-error and null-abort prior as PublicInstance.plan. -/
def plan (isBoolean : Q → Bool) : List (List Q × Nat) → List Bool → List Action
 | [], _ => []
 | (p,n)::rest, failures =>
  if n ≠ 1024 then [] else
  let t := (p.reverse.takeWhile isBoolean).length
  let bytes := 24 * 2^(p.length-t)
  if failures.headD false then [.allocate bytes 8,.abort bytes 8] else
  [.allocate bytes 8,.deallocate bytes 8] ++ plan isBoolean rest failures.tail

def calls (wirePoints : List Q → List (List Q)) (i : Input) : List (List Q × Nat) :=
 (wirePoints i.point).flatMap fun p => i.columns.map fun c => (p,c.length)

/-- Ordinary full-coordinate integer-row multilinear evaluation. -/
def dense {K : Type} [Field K] (decode : Q → K) (zero : Q)
 (point column : List Q) : K :=
 ∑ r : Fin 1024,
  (∏ j : Fin 10,
   if r.val.testBit (9-j.val) then decode (point[j.val]?.getD zero)
   else 1-decode (point[j.val]?.getD zero)) * decode (column[r.val]?.getD zero)

/-- Complete observable output and the post-world, also on failure/divergence. -/
structure Execution (K W : Type) where
 result : Result (Option K)
 world : W
 trace : List Action

/-- Actual accepted builder/parser/sampler inputs, before wire transforms. -/
def PV_OWNM_Link_ActualInput (wirePoints : List Q → List (List Q)) (i : Input) : Prop :=
 i.point.length = 10 ∧
 (∀ p ∈ wirePoints i.point, p.length = 10 ∧ ∀ q ∈ p, Canon q) ∧
 (∀ c ∈ i.columns, ∀ q ∈ c, Canon q)

/-- Scalar source equation only; contains no native world or resource equality. -/
def PV_OWNM_Link_SourceDense {K : Type} [Field K] (decode : Q → K) (zero : Q)
 (source222 : List Q → List Q → Result (Option Q)) : Prop :=
 ∀ p c, p.length = 10 → (∀ q ∈ p, Canon q) → (∀ q ∈ c, Canon q) →
 (do let v ← source222 p c; ok (v.map decode)) =
 ok (if c.length ≠ 1024 then none else some (dense decode zero p c))

/-- Operational reconstruction of the callback point, including public counters. -/
def PV_OWNM_Link_Transcript879 (reconstruct879 : Public → List Q) (i : Input) : Prop :=
 i.site = .callback879 → i.point = reconstruct879 i.pubData

/-- Operational reconstruction of final alpha from the published byte frames. -/
def PV_OWNM_Link_Transcript890 (reconstruct890 : Public → List Q) (i : Input) : Prop :=
 i.site = .final890 → i.point = reconstruct890 i.pubData

/-- The owned context retains allocator error/abort/divergence and the post-world.
The association is to the raw source value, never to dense evaluation. The
trace clause holds for every value continuation, including error and div. -/
def PV_OWNM_Link_OwnedPublicPlan {K W : Type} (decode : Q → K)
 (source222 : List Q → List Q → Result (Option Q))
 (wirePoints : List Q → List (List Q)) (isBoolean : Q → Bool)
 (native : Input → Nat → Execution K W)
 (owned : Input → Nat → Result (Option K) → Execution K W)
 (failures : List Bool) (i : Input) : Prop :=
 (∀ lane c, i.columns[lane]? = some c →
  native i lane = owned i lane (do let v ← source222 i.point c; ok (v.map decode))) ∧
 (∀ lane value, (owned i lane value).trace = plan isBoolean (calls wirePoints i) failures)

/-- Conditional restoration composition. All missing source instances are named
links above. Equality of Execution preserves the complete Result and post-world;
resource equality compares the very executions used in the value equation. -/
theorem restore {K W : Type} [Field K] (decode : Q → K) (zero : Q)
 (source222 : List Q → List Q → Result (Option Q))
 (wirePoints : List Q → List (List Q)) (isBoolean : Q → Bool)
 (reconstruct879 reconstruct890 : Public → List Q)
 (native : Input → Nat → Execution K W)
 (owned : Input → Nat → Result (Option K) → Execution K W)
 (failures : List Bool) (left right : Input)
 (inputL : PV_OWNM_Link_ActualInput wirePoints left)
 (inputR : PV_OWNM_Link_ActualInput wirePoints right)
 (commute : PV_OWNM_Link_SourceDense decode zero source222)
 (cbL : PV_OWNM_Link_Transcript879 reconstruct879 left)
 (cbR : PV_OWNM_Link_Transcript879 reconstruct879 right)
 (finalL : PV_OWNM_Link_Transcript890 reconstruct890 left)
 (finalR : PV_OWNM_Link_Transcript890 reconstruct890 right)
 (ownedL : PV_OWNM_Link_OwnedPublicPlan decode source222 wirePoints isBoolean native owned failures left)
 (ownedR : PV_OWNM_Link_OwnedPublicPlan decode source222 wirePoints isBoolean native owned failures right)
 (samePublic : left.pubData = right.pubData) (sameSite : left.site = right.site)
 (sameLengths : left.columns.map List.length = right.columns.map List.length)
 (wireSelf : ∀ p, p ∈ wirePoints p) :
 (∀ lane c, left.columns[lane]? = some c →
  native left lane = owned left lane
   (ok (if c.length ≠ 1024 then none else some (dense decode zero left.point c)))) ∧
 (∀ lane c, right.columns[lane]? = some c →
  native right lane = owned right lane
   (ok (if c.length ≠ 1024 then none else some (dense decode zero right.point c)))) ∧
 (∀ laneL laneR cL cR, left.columns[laneL]? = some cL →
  right.columns[laneR]? = some cR →
  (native left laneL).trace = (native right laneR).trace) := by
 have points : left.point = right.point := by
  cases hs : left.site with
  | callback879 =>
   have hr : right.site = .callback879 := sameSite.symm.trans hs
   rw [cbL hs,cbR hr,samePublic]
  | final890 =>
   have hr : right.site = .final890 := sameSite.symm.trans hs
   rw [finalL hs,finalR hr,samePublic]
 have valueL : ∀ lane c, left.columns[lane]? = some c →
  native left lane = owned left lane
   (ok (if c.length ≠ 1024 then none else some (dense decode zero left.point c))) := by
  intro lane c hc
  rw [ownedL.1 lane c hc]
  rw [commute left.point c inputL.1 (inputL.2.1 _ (wireSelf _)).2
   (inputL.2.2 c (List.mem_of_getElem? hc))]
 have valueR : ∀ lane c, right.columns[lane]? = some c →
  native right lane = owned right lane
   (ok (if c.length ≠ 1024 then none else some (dense decode zero right.point c))) := by
  intro lane c hc
  rw [ownedR.1 lane c hc]
  rw [commute right.point c inputR.1 (inputR.2.1 _ (wireSelf _)).2
   (inputR.2.2 c (List.mem_of_getElem? hc))]
 refine ⟨valueL,valueR,?_⟩
 intro laneL laneR cL cR hcL hcR
 rw [ownedL.1 laneL cL hcL,ownedR.1 laneR cR hcR,ownedL.2,ownedR.2]
 have callEq : calls wirePoints left = calls wirePoints right := by
  simp only [calls,← List.map_map]
  rw [points,sameLengths]
 rw [callEq]

#print restore
#print axioms restore
end R1Z.PV_OWNM_V239
