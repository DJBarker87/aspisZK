import AspisV8R19.R748GatherExpand04
/-! Generated sourceGather expansions from named ten-fuel schedules. -/
set_option autoImplicit false
namespace AspisV8R19.R748GatherExpand05
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
variable {F : Type*} [CommRing F]
lemma gather382 (half : F) (w : Nat → F) :
    sourceGather half w 382 = half^0*w 383 := by
  rw [sourceGather_powers, loop382]
  simp <;> ring
#print axioms gather382

lemma gather383 (half : F) (w : Nat → F) :
    sourceGather half w 383 = half*w 382 + half^2*w 380 + half^3*w 376 + half^4*w 368 + half^5*w 352 + half^6*w 320 + half^7*w 256 + half^7*w 384 := by
  rw [sourceGather_powers, loop383]
  simp <;> ring
#print axioms gather383

lemma gather440 (half : F) (w : Nat → F) :
    sourceGather half w 440 = half^0*w 441 := by
  rw [sourceGather_powers, loop440]
  simp <;> ring
#print axioms gather440

lemma gather441 (half : F) (w : Nat → F) :
    sourceGather half w 441 = half*w 440 + half*w 442 := by
  rw [sourceGather_powers, loop441]
  simp <;> ring
#print axioms gather441

lemma gather442 (half : F) (w : Nat → F) :
    sourceGather half w 442 = half^0*w 443 := by
  rw [sourceGather_powers, loop442]
  simp <;> ring
#print axioms gather442

lemma gather443 (half : F) (w : Nat → F) :
    sourceGather half w 443 = half*w 442 + half^2*w 440 + half^2*w 444 := by
  rw [sourceGather_powers, loop443]
  simp <;> ring
#print axioms gather443

lemma gather444 (half : F) (w : Nat → F) :
    sourceGather half w 444 = half^0*w 445 := by
  rw [sourceGather_powers, loop444]
  simp <;> ring
#print axioms gather444

lemma gather445 (half : F) (w : Nat → F) :
    sourceGather half w 445 = half*w 444 + half*w 446 := by
  rw [sourceGather_powers, loop445]
  simp <;> ring
#print axioms gather445

lemma gather446 (half : F) (w : Nat → F) :
    sourceGather half w 446 = half^0*w 447 := by
  rw [sourceGather_powers, loop446]
  simp <;> ring
#print axioms gather446

lemma gather447 (half : F) (w : Nat → F) :
    sourceGather half w 447 = half*w 446 + half^2*w 444 + half^3*w 440 + half^4*w 432 + half^5*w 416 + half^6*w 384 + half^6*w 448 := by
  rw [sourceGather_powers, loop447]
  simp <;> ring
#print axioms gather447

lemma gather450 (half : F) (w : Nat → F) :
    sourceGather half w 450 = half^0*w 451 := by
  rw [sourceGather_powers, loop450]
  simp <;> ring
#print axioms gather450

lemma gather451 (half : F) (w : Nat → F) :
    sourceGather half w 451 = half*w 450 + half^2*w 448 + half^2*w 452 := by
  rw [sourceGather_powers, loop451]
  simp <;> ring
#print axioms gather451

lemma gather452 (half : F) (w : Nat → F) :
    sourceGather half w 452 = half^0*w 453 := by
  rw [sourceGather_powers, loop452]
  simp <;> ring
#print axioms gather452

lemma gather453 (half : F) (w : Nat → F) :
    sourceGather half w 453 = half*w 452 + half*w 454 := by
  rw [sourceGather_powers, loop453]
  simp <;> ring
#print axioms gather453

lemma gather454 (half : F) (w : Nat → F) :
    sourceGather half w 454 = half^0*w 455 := by
  rw [sourceGather_powers, loop454]
  simp <;> ring
#print axioms gather454

lemma gather455 (half : F) (w : Nat → F) :
    sourceGather half w 455 = half*w 454 + half^2*w 452 + half^3*w 448 + half^3*w 456 := by
  rw [sourceGather_powers, loop455]
  simp <;> ring
#print axioms gather455

lemma gather456 (half : F) (w : Nat → F) :
    sourceGather half w 456 = half^0*w 457 := by
  rw [sourceGather_powers, loop456]
  simp <;> ring
#print axioms gather456

lemma gather457 (half : F) (w : Nat → F) :
    sourceGather half w 457 = half*w 456 + half*w 458 := by
  rw [sourceGather_powers, loop457]
  simp <;> ring
#print axioms gather457

lemma gather458 (half : F) (w : Nat → F) :
    sourceGather half w 458 = half^0*w 459 := by
  rw [sourceGather_powers, loop458]
  simp <;> ring
#print axioms gather458

lemma gather459 (half : F) (w : Nat → F) :
    sourceGather half w 459 = half*w 458 + half^2*w 456 + half^2*w 460 := by
  rw [sourceGather_powers, loop459]
  simp <;> ring
#print axioms gather459

lemma gather460 (half : F) (w : Nat → F) :
    sourceGather half w 460 = half^0*w 461 := by
  rw [sourceGather_powers, loop460]
  simp <;> ring
#print axioms gather460

lemma gather461 (half : F) (w : Nat → F) :
    sourceGather half w 461 = half*w 460 + half*w 462 := by
  rw [sourceGather_powers, loop461]
  simp <;> ring
#print axioms gather461

lemma gather462 (half : F) (w : Nat → F) :
    sourceGather half w 462 = half^0*w 463 := by
  rw [sourceGather_powers, loop462]
  simp <;> ring
#print axioms gather462

lemma gather463 (half : F) (w : Nat → F) :
    sourceGather half w 463 = half*w 462 + half^2*w 460 + half^3*w 456 + half^4*w 448 + half^4*w 464 := by
  rw [sourceGather_powers, loop463]
  simp <;> ring
#print axioms gather463

lemma gather464 (half : F) (w : Nat → F) :
    sourceGather half w 464 = half^0*w 465 := by
  rw [sourceGather_powers, loop464]
  simp <;> ring
#print axioms gather464

lemma gather465 (half : F) (w : Nat → F) :
    sourceGather half w 465 = half*w 464 + half*w 466 := by
  rw [sourceGather_powers, loop465]
  simp <;> ring
#print axioms gather465

lemma gather466 (half : F) (w : Nat → F) :
    sourceGather half w 466 = half^0*w 467 := by
  rw [sourceGather_powers, loop466]
  simp <;> ring
#print axioms gather466

lemma gather467 (half : F) (w : Nat → F) :
    sourceGather half w 467 = half*w 466 + half^2*w 464 + half^2*w 468 := by
  rw [sourceGather_powers, loop467]
  simp <;> ring
#print axioms gather467

lemma gather468 (half : F) (w : Nat → F) :
    sourceGather half w 468 = half^0*w 469 := by
  rw [sourceGather_powers, loop468]
  simp <;> ring
#print axioms gather468

lemma gather469 (half : F) (w : Nat → F) :
    sourceGather half w 469 = half*w 468 + half*w 470 := by
  rw [sourceGather_powers, loop469]
  simp <;> ring
#print axioms gather469

lemma gather470 (half : F) (w : Nat → F) :
    sourceGather half w 470 = half^0*w 471 := by
  rw [sourceGather_powers, loop470]
  simp <;> ring
#print axioms gather470

lemma gather471 (half : F) (w : Nat → F) :
    sourceGather half w 471 = half*w 470 + half^2*w 468 + half^3*w 464 + half^3*w 472 := by
  rw [sourceGather_powers, loop471]
  simp <;> ring
#print axioms gather471
end AspisV8R19.R748GatherExpand05
