import AspisV8R19.R748GatherLoop07
/-! Generated sourceGather expansions from named ten-fuel schedules. -/
set_option autoImplicit false
namespace AspisV8R19.R748GatherExpand00
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
variable {F : Type*} [CommRing F]
lemma gather32 (half : F) (w : Nat → F) :
    sourceGather half w 32 = half^0*w 33 := by
  rw [sourceGather_powers, loop32]
  simp <;> ring
#print axioms gather32

lemma gather40 (half : F) (w : Nat → F) :
    sourceGather half w 40 = half^0*w 41 := by
  rw [sourceGather_powers, loop40]
  simp <;> ring
#print axioms gather40

lemma gather44 (half : F) (w : Nat → F) :
    sourceGather half w 44 = half^0*w 45 := by
  rw [sourceGather_powers, loop44]
  simp <;> ring
#print axioms gather44

lemma gather46 (half : F) (w : Nat → F) :
    sourceGather half w 46 = half^0*w 47 := by
  rw [sourceGather_powers, loop46]
  simp <;> ring
#print axioms gather46

lemma gather47 (half : F) (w : Nat → F) :
    sourceGather half w 47 = half*w 46 + half^2*w 44 + half^3*w 40 + half^4*w 32 + half^4*w 48 := by
  rw [sourceGather_powers, loop47]
  simp <;> ring
#print axioms gather47

lemma gather48 (half : F) (w : Nat → F) :
    sourceGather half w 48 = half^0*w 49 := by
  rw [sourceGather_powers, loop48]
  simp <;> ring
#print axioms gather48

lemma gather49 (half : F) (w : Nat → F) :
    sourceGather half w 49 = half*w 48 + half*w 50 := by
  rw [sourceGather_powers, loop49]
  simp <;> ring
#print axioms gather49

lemma gather50 (half : F) (w : Nat → F) :
    sourceGather half w 50 = half^0*w 51 := by
  rw [sourceGather_powers, loop50]
  simp <;> ring
#print axioms gather50

lemma gather52 (half : F) (w : Nat → F) :
    sourceGather half w 52 = half^0*w 53 := by
  rw [sourceGather_powers, loop52]
  simp <;> ring
#print axioms gather52

lemma gather54 (half : F) (w : Nat → F) :
    sourceGather half w 54 = half^0*w 55 := by
  rw [sourceGather_powers, loop54]
  simp <;> ring
#print axioms gather54

lemma gather55 (half : F) (w : Nat → F) :
    sourceGather half w 55 = half*w 54 + half^2*w 52 + half^3*w 48 + half^3*w 56 := by
  rw [sourceGather_powers, loop55]
  simp <;> ring
#print axioms gather55

lemma gather56 (half : F) (w : Nat → F) :
    sourceGather half w 56 = half^0*w 57 := by
  rw [sourceGather_powers, loop56]
  simp <;> ring
#print axioms gather56

lemma gather57 (half : F) (w : Nat → F) :
    sourceGather half w 57 = half*w 56 + half*w 58 := by
  rw [sourceGather_powers, loop57]
  simp <;> ring
#print axioms gather57

lemma gather58 (half : F) (w : Nat → F) :
    sourceGather half w 58 = half^0*w 59 := by
  rw [sourceGather_powers, loop58]
  simp <;> ring
#print axioms gather58

lemma gather59 (half : F) (w : Nat → F) :
    sourceGather half w 59 = half*w 58 + half^2*w 56 + half^2*w 60 := by
  rw [sourceGather_powers, loop59]
  simp <;> ring
#print axioms gather59

lemma gather60 (half : F) (w : Nat → F) :
    sourceGather half w 60 = half^0*w 61 := by
  rw [sourceGather_powers, loop60]
  simp <;> ring
#print axioms gather60

lemma gather61 (half : F) (w : Nat → F) :
    sourceGather half w 61 = half*w 60 + half*w 62 := by
  rw [sourceGather_powers, loop61]
  simp <;> ring
#print axioms gather61

lemma gather62 (half : F) (w : Nat → F) :
    sourceGather half w 62 = half^0*w 63 := by
  rw [sourceGather_powers, loop62]
  simp <;> ring
#print axioms gather62

lemma gather63 (half : F) (w : Nat → F) :
    sourceGather half w 63 = half*w 62 + half^2*w 60 + half^3*w 56 + half^4*w 48 + half^5*w 32 + half^6*w 0 + half^6*w 64 := by
  rw [sourceGather_powers, loop63]
  simp <;> ring
#print axioms gather63

lemma gather65 (half : F) (w : Nat → F) :
    sourceGather half w 65 = half*w 64 + half*w 66 := by
  rw [sourceGather_powers, loop65]
  simp <;> ring
#print axioms gather65

lemma gather66 (half : F) (w : Nat → F) :
    sourceGather half w 66 = half^0*w 67 := by
  rw [sourceGather_powers, loop66]
  simp <;> ring
#print axioms gather66

lemma gather67 (half : F) (w : Nat → F) :
    sourceGather half w 67 = half*w 66 + half^2*w 64 + half^2*w 68 := by
  rw [sourceGather_powers, loop67]
  simp <;> ring
#print axioms gather67

lemma gather68 (half : F) (w : Nat → F) :
    sourceGather half w 68 = half^0*w 69 := by
  rw [sourceGather_powers, loop68]
  simp <;> ring
#print axioms gather68

lemma gather69 (half : F) (w : Nat → F) :
    sourceGather half w 69 = half*w 68 + half*w 70 := by
  rw [sourceGather_powers, loop69]
  simp <;> ring
#print axioms gather69

lemma gather70 (half : F) (w : Nat → F) :
    sourceGather half w 70 = half^0*w 71 := by
  rw [sourceGather_powers, loop70]
  simp <;> ring
#print axioms gather70

lemma gather71 (half : F) (w : Nat → F) :
    sourceGather half w 71 = half*w 70 + half^2*w 68 + half^3*w 64 + half^3*w 72 := by
  rw [sourceGather_powers, loop71]
  simp <;> ring
#print axioms gather71

lemma gather72 (half : F) (w : Nat → F) :
    sourceGather half w 72 = half^0*w 73 := by
  rw [sourceGather_powers, loop72]
  simp <;> ring
#print axioms gather72

lemma gather73 (half : F) (w : Nat → F) :
    sourceGather half w 73 = half*w 72 + half*w 74 := by
  rw [sourceGather_powers, loop73]
  simp <;> ring
#print axioms gather73

lemma gather74 (half : F) (w : Nat → F) :
    sourceGather half w 74 = half^0*w 75 := by
  rw [sourceGather_powers, loop74]
  simp <;> ring
#print axioms gather74

lemma gather75 (half : F) (w : Nat → F) :
    sourceGather half w 75 = half*w 74 + half^2*w 72 + half^2*w 76 := by
  rw [sourceGather_powers, loop75]
  simp <;> ring
#print axioms gather75

lemma gather76 (half : F) (w : Nat → F) :
    sourceGather half w 76 = half^0*w 77 := by
  rw [sourceGather_powers, loop76]
  simp <;> ring
#print axioms gather76

lemma gather77 (half : F) (w : Nat → F) :
    sourceGather half w 77 = half*w 76 + half*w 78 := by
  rw [sourceGather_powers, loop77]
  simp <;> ring
#print axioms gather77
end AspisV8R19.R748GatherExpand00
