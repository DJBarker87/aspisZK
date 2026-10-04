import AspisV8R19.R748GatherExpand07
/-! Generated nested sourceGather expansions for odd pointWeight indices. -/
set_option autoImplicit false
namespace AspisV8R19.R748GatherNested00
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
open AspisV8R19.R748GatherExpand07
variable {F : Type*} [CommRing F]
lemma gatherGather0 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 0 = half*w 0 + half*w 2 := by
  rw [gather0, gather1] <;> simp <;> ring
#print axioms gatherGather0

lemma gatherGather46 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 46 = half*w 46 + half^2*w 44 + half^3*w 40 + half^4*w 32 + half^4*w 48 := by
  rw [gather46, gather47] <;> simp <;> ring
#print axioms gatherGather46

lemma gatherGather47 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 47 = half*w 47 + half^2*w 45 + half^3*w 41 + half^4*w 33 + half^4*w 49 := by
  rw [gather47, gather32, gather40, gather44, gather46, gather48] <;> simp <;> ring
#print axioms gatherGather47

lemma gatherGather48 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 48 = half*w 48 + half*w 50 := by
  rw [gather48, gather49] <;> simp <;> ring
#print axioms gatherGather48

lemma gatherGather49 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 49 = half*w 49 + half*w 51 := by
  rw [gather49, gather48, gather50] <;> simp <;> ring
#print axioms gatherGather49

lemma gatherGather55 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 55 = half*w 55 + half^2*w 53 + half^3*w 49 + half^3*w 57 := by
  rw [gather55, gather48, gather52, gather54, gather56] <;> simp <;> ring
#print axioms gatherGather55

lemma gatherGather58 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 58 = half*w 58 + half^2*w 56 + half^2*w 60 := by
  rw [gather58, gather59] <;> simp <;> ring
#print axioms gatherGather58

lemma gatherGather60 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 60 = half*w 60 + half*w 62 := by
  rw [gather60, gather61] <;> simp <;> ring
#print axioms gatherGather60

lemma gatherGather62 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 62 = half*w 62 + half^2*w 60 + half^3*w 56 + half^4*w 48 + half^5*w 32 + half^6*w 0 + half^6*w 64 := by
  rw [gather62, gather63] <;> simp <;> ring
#print axioms gatherGather62

lemma gatherGather64 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 64 = half*w 64 + half*w 66 := by
  rw [gather64, gather65] <;> simp <;> ring
#print axioms gatherGather64

lemma gatherGather66 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 66 = half*w 66 + half^2*w 64 + half^2*w 68 := by
  rw [gather66, gather67] <;> simp <;> ring
#print axioms gatherGather66

lemma gatherGather68 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 68 = half*w 68 + half*w 70 := by
  rw [gather68, gather69] <;> simp <;> ring
#print axioms gatherGather68

lemma gatherGather70 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 70 = half*w 70 + half^2*w 68 + half^3*w 64 + half^3*w 72 := by
  rw [gather70, gather71] <;> simp <;> ring
#print axioms gatherGather70

lemma gatherGather72 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 72 = half*w 72 + half*w 74 := by
  rw [gather72, gather73] <;> simp <;> ring
#print axioms gatherGather72

lemma gatherGather74 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 74 = half*w 74 + half^2*w 72 + half^2*w 76 := by
  rw [gather74, gather75] <;> simp <;> ring
#print axioms gatherGather74

lemma gatherGather76 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 76 = half*w 76 + half*w 78 := by
  rw [gather76, gather77] <;> simp <;> ring
#print axioms gatherGather76

lemma gatherGather78 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 78 = half*w 78 + half^2*w 76 + half^3*w 72 + half^4*w 64 + half^4*w 80 := by
  rw [gather78, gather79] <;> simp <;> ring
#print axioms gatherGather78

lemma gatherGather80 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 80 = half*w 80 + half*w 82 := by
  rw [gather80, gather81] <;> simp <;> ring
#print axioms gatherGather80

lemma gatherGather82 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 82 = half*w 82 + half^2*w 80 + half^2*w 84 := by
  rw [gather82, gather83] <;> simp <;> ring
#print axioms gatherGather82

lemma gatherGather84 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 84 = half*w 84 + half*w 86 := by
  rw [gather84, gather85] <;> simp <;> ring
#print axioms gatherGather84

lemma gatherGather86 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 86 = half*w 86 + half^2*w 84 + half^3*w 80 + half^3*w 88 := by
  rw [gather86, gather87] <;> simp <;> ring
#print axioms gatherGather86

lemma gatherGather88 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 88 = half*w 88 + half*w 90 := by
  rw [gather88, gather89] <;> simp <;> ring
#print axioms gatherGather88

lemma gatherGather90 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 90 = half*w 90 + half^2*w 88 + half^2*w 92 := by
  rw [gather90, gather91] <;> simp <;> ring
#print axioms gatherGather90

lemma gatherGather92 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 92 = half*w 92 + half*w 94 := by
  rw [gather92, gather93] <;> simp <;> ring
#print axioms gatherGather92

lemma gatherGather98 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 98 = half*w 98 + half^2*w 96 + half^2*w 100 := by
  rw [gather98, gather99] <;> simp <;> ring
#print axioms gatherGather98

lemma gatherGather100 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 100 = half*w 100 + half*w 102 := by
  rw [gather100, gather101] <;> simp <;> ring
#print axioms gatherGather100

lemma gatherGather102 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 102 = half*w 102 + half^2*w 100 + half^3*w 96 + half^3*w 104 := by
  rw [gather102, gather103] <;> simp <;> ring
#print axioms gatherGather102

lemma gatherGather104 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 104 = half*w 104 + half*w 106 := by
  rw [gather104, gather105] <;> simp <;> ring
#print axioms gatherGather104

lemma gatherGather106 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 106 = half*w 106 + half^2*w 104 + half^2*w 108 := by
  rw [gather106, gather107] <;> simp <;> ring
#print axioms gatherGather106

lemma gatherGather108 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 108 = half*w 108 + half*w 110 := by
  rw [gather108, gather109] <;> simp <;> ring
#print axioms gatherGather108

lemma gatherGather110 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 110 = half*w 110 + half^2*w 108 + half^3*w 104 + half^4*w 96 + half^4*w 112 := by
  rw [gather110, gather111] <;> simp <;> ring
#print axioms gatherGather110

lemma gatherGather112 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 112 = half*w 112 + half*w 114 := by
  rw [gather112, gather113] <;> simp <;> ring
#print axioms gatherGather112
end AspisV8R19.R748GatherNested00
