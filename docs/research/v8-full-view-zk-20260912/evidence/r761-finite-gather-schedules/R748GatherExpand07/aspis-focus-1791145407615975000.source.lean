import AspisV8R19.R748GatherExpand06
/-! Generated sourceGather expansions from named ten-fuel schedules. -/
set_option autoImplicit false
namespace AspisV8R19.R748GatherExpand07
open AspisV8R17
open AspisV8R19.R742SourceObservationHom
open AspisV8R19.R748FiniteGatherSchedules
open AspisV8R19.R748SchedulePrototype
open AspisV8R19.R748GatherLoop00
open AspisV8R19.R748GatherLoop01
open AspisV8R19.R748GatherLoop02
open AspisV8R19.R748GatherLoop03
open AspisV8R19.R748GatherLoop04
open AspisV8R19.R748GatherLoop05
open AspisV8R19.R748GatherLoop06
open AspisV8R19.R748GatherLoop07
open AspisV8R19.R748GatherExpand00
open AspisV8R19.R748GatherExpand01
open AspisV8R19.R748GatherExpand02
open AspisV8R19.R748GatherExpand03
open AspisV8R19.R748GatherExpand04
open AspisV8R19.R748GatherExpand05
open AspisV8R19.R748GatherExpand06
variable {F : Type*} [CommRing F]
lemma gather504 (half : F) (w : Nat → F) :
    sourceGather half w 504 = half^0*w 505 := by
  rw [sourceGather_powers, loop504]
  simp <;> ring
#print axioms gather504

lemma gather505 (half : F) (w : Nat → F) :
    sourceGather half w 505 = half*w 504 + half*w 506 := by
  rw [sourceGather_powers, loop505]
  simp <;> ring
#print axioms gather505

lemma gather506 (half : F) (w : Nat → F) :
    sourceGather half w 506 = half^0*w 507 := by
  rw [sourceGather_powers, loop506]
  simp <;> ring
#print axioms gather506

lemma gather507 (half : F) (w : Nat → F) :
    sourceGather half w 507 = half*w 506 + half^2*w 504 + half^2*w 508 := by
  rw [sourceGather_powers, loop507]
  simp <;> ring
#print axioms gather507

lemma gather508 (half : F) (w : Nat → F) :
    sourceGather half w 508 = half^0*w 509 := by
  rw [sourceGather_powers, loop508]
  simp <;> ring
#print axioms gather508

lemma gather509 (half : F) (w : Nat → F) :
    sourceGather half w 509 = half*w 508 + half*w 510 := by
  rw [sourceGather_powers, loop509]
  simp <;> ring
#print axioms gather509

lemma gather510 (half : F) (w : Nat → F) :
    sourceGather half w 510 = half^0*w 511 := by
  rw [sourceGather_powers, loop510]
  simp <;> ring
#print axioms gather510
end AspisV8R19.R748GatherExpand07
