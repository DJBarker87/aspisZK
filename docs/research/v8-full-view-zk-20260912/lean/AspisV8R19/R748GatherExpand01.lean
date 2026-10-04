import AspisV8R19.R748GatherExpand00
/-! Generated sourceGather expansions from named ten-fuel schedules. -/
set_option autoImplicit false
namespace AspisV8R19.R748GatherExpand01
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
variable {F : Type*} [CommRing F]
lemma gather78 (half : F) (w : Nat → F) :
    sourceGather half w 78 = half^0*w 79 := by
  rw [sourceGather_powers, loop78]
  simp <;> ring
#print axioms gather78

lemma gather79 (half : F) (w : Nat → F) :
    sourceGather half w 79 = half*w 78 + half^2*w 76 + half^3*w 72 + half^4*w 64 + half^4*w 80 := by
  rw [sourceGather_powers, loop79]
  simp <;> ring
#print axioms gather79

lemma gather81 (half : F) (w : Nat → F) :
    sourceGather half w 81 = half*w 80 + half*w 82 := by
  rw [sourceGather_powers, loop81]
  simp <;> ring
#print axioms gather81

lemma gather82 (half : F) (w : Nat → F) :
    sourceGather half w 82 = half^0*w 83 := by
  rw [sourceGather_powers, loop82]
  simp <;> ring
#print axioms gather82

lemma gather83 (half : F) (w : Nat → F) :
    sourceGather half w 83 = half*w 82 + half^2*w 80 + half^2*w 84 := by
  rw [sourceGather_powers, loop83]
  simp <;> ring
#print axioms gather83

lemma gather84 (half : F) (w : Nat → F) :
    sourceGather half w 84 = half^0*w 85 := by
  rw [sourceGather_powers, loop84]
  simp <;> ring
#print axioms gather84

lemma gather85 (half : F) (w : Nat → F) :
    sourceGather half w 85 = half*w 84 + half*w 86 := by
  rw [sourceGather_powers, loop85]
  simp <;> ring
#print axioms gather85

lemma gather86 (half : F) (w : Nat → F) :
    sourceGather half w 86 = half^0*w 87 := by
  rw [sourceGather_powers, loop86]
  simp <;> ring
#print axioms gather86

lemma gather87 (half : F) (w : Nat → F) :
    sourceGather half w 87 = half*w 86 + half^2*w 84 + half^3*w 80 + half^3*w 88 := by
  rw [sourceGather_powers, loop87]
  simp <;> ring
#print axioms gather87

lemma gather89 (half : F) (w : Nat → F) :
    sourceGather half w 89 = half*w 88 + half*w 90 := by
  rw [sourceGather_powers, loop89]
  simp <;> ring
#print axioms gather89

lemma gather90 (half : F) (w : Nat → F) :
    sourceGather half w 90 = half^0*w 91 := by
  rw [sourceGather_powers, loop90]
  simp <;> ring
#print axioms gather90

lemma gather91 (half : F) (w : Nat → F) :
    sourceGather half w 91 = half*w 90 + half^2*w 88 + half^2*w 92 := by
  rw [sourceGather_powers, loop91]
  simp <;> ring
#print axioms gather91

lemma gather93 (half : F) (w : Nat → F) :
    sourceGather half w 93 = half*w 92 + half*w 94 := by
  rw [sourceGather_powers, loop93]
  simp <;> ring
#print axioms gather93

lemma gather97 (half : F) (w : Nat → F) :
    sourceGather half w 97 = half*w 96 + half*w 98 := by
  rw [sourceGather_powers, loop97]
  simp <;> ring
#print axioms gather97

lemma gather98 (half : F) (w : Nat → F) :
    sourceGather half w 98 = half^0*w 99 := by
  rw [sourceGather_powers, loop98]
  simp <;> ring
#print axioms gather98

lemma gather99 (half : F) (w : Nat → F) :
    sourceGather half w 99 = half*w 98 + half^2*w 96 + half^2*w 100 := by
  rw [sourceGather_powers, loop99]
  simp <;> ring
#print axioms gather99

lemma gather100 (half : F) (w : Nat → F) :
    sourceGather half w 100 = half^0*w 101 := by
  rw [sourceGather_powers, loop100]
  simp <;> ring
#print axioms gather100

lemma gather101 (half : F) (w : Nat → F) :
    sourceGather half w 101 = half*w 100 + half*w 102 := by
  rw [sourceGather_powers, loop101]
  simp <;> ring
#print axioms gather101

lemma gather102 (half : F) (w : Nat → F) :
    sourceGather half w 102 = half^0*w 103 := by
  rw [sourceGather_powers, loop102]
  simp <;> ring
#print axioms gather102

lemma gather103 (half : F) (w : Nat → F) :
    sourceGather half w 103 = half*w 102 + half^2*w 100 + half^3*w 96 + half^3*w 104 := by
  rw [sourceGather_powers, loop103]
  simp <;> ring
#print axioms gather103

lemma gather104 (half : F) (w : Nat → F) :
    sourceGather half w 104 = half^0*w 105 := by
  rw [sourceGather_powers, loop104]
  simp <;> ring
#print axioms gather104

lemma gather105 (half : F) (w : Nat → F) :
    sourceGather half w 105 = half*w 104 + half*w 106 := by
  rw [sourceGather_powers, loop105]
  simp <;> ring
#print axioms gather105

lemma gather106 (half : F) (w : Nat → F) :
    sourceGather half w 106 = half^0*w 107 := by
  rw [sourceGather_powers, loop106]
  simp <;> ring
#print axioms gather106

lemma gather107 (half : F) (w : Nat → F) :
    sourceGather half w 107 = half*w 106 + half^2*w 104 + half^2*w 108 := by
  rw [sourceGather_powers, loop107]
  simp <;> ring
#print axioms gather107

lemma gather108 (half : F) (w : Nat → F) :
    sourceGather half w 108 = half^0*w 109 := by
  rw [sourceGather_powers, loop108]
  simp <;> ring
#print axioms gather108

lemma gather109 (half : F) (w : Nat → F) :
    sourceGather half w 109 = half*w 108 + half*w 110 := by
  rw [sourceGather_powers, loop109]
  simp <;> ring
#print axioms gather109

lemma gather110 (half : F) (w : Nat → F) :
    sourceGather half w 110 = half^0*w 111 := by
  rw [sourceGather_powers, loop110]
  simp <;> ring
#print axioms gather110

lemma gather111 (half : F) (w : Nat → F) :
    sourceGather half w 111 = half*w 110 + half^2*w 108 + half^3*w 104 + half^4*w 96 + half^4*w 112 := by
  rw [sourceGather_powers, loop111]
  simp <;> ring
#print axioms gather111

lemma gather112 (half : F) (w : Nat → F) :
    sourceGather half w 112 = half^0*w 113 := by
  rw [sourceGather_powers, loop112]
  simp <;> ring
#print axioms gather112

lemma gather113 (half : F) (w : Nat → F) :
    sourceGather half w 113 = half*w 112 + half*w 114 := by
  rw [sourceGather_powers, loop113]
  simp <;> ring
#print axioms gather113

lemma gather114 (half : F) (w : Nat → F) :
    sourceGather half w 114 = half^0*w 115 := by
  rw [sourceGather_powers, loop114]
  simp <;> ring
#print axioms gather114

lemma gather115 (half : F) (w : Nat → F) :
    sourceGather half w 115 = half*w 114 + half^2*w 112 + half^2*w 116 := by
  rw [sourceGather_powers, loop115]
  simp <;> ring
#print axioms gather115
end AspisV8R19.R748GatherExpand01
