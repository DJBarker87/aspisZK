import AspisV8R19.R748GatherExpand01
/-! Generated sourceGather expansions from named ten-fuel schedules. -/
set_option autoImplicit false
namespace AspisV8R19.R748GatherExpand02
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
variable {F : Type*} [CommRing F]
lemma gather116 (half : F) (w : Nat → F) :
    sourceGather half w 116 = half^0*w 117 := by
  rw [sourceGather_powers, loop116]
  simp <;> ring
#print axioms gather116

lemma gather117 (half : F) (w : Nat → F) :
    sourceGather half w 117 = half*w 116 + half*w 118 := by
  rw [sourceGather_powers, loop117]
  simp <;> ring
#print axioms gather117

lemma gather118 (half : F) (w : Nat → F) :
    sourceGather half w 118 = half^0*w 119 := by
  rw [sourceGather_powers, loop118]
  simp <;> ring
#print axioms gather118

lemma gather119 (half : F) (w : Nat → F) :
    sourceGather half w 119 = half*w 118 + half^2*w 116 + half^3*w 112 + half^3*w 120 := by
  rw [sourceGather_powers, loop119]
  simp <;> ring
#print axioms gather119

lemma gather120 (half : F) (w : Nat → F) :
    sourceGather half w 120 = half^0*w 121 := by
  rw [sourceGather_powers, loop120]
  simp <;> ring
#print axioms gather120

lemma gather121 (half : F) (w : Nat → F) :
    sourceGather half w 121 = half*w 120 + half*w 122 := by
  rw [sourceGather_powers, loop121]
  simp <;> ring
#print axioms gather121

lemma gather122 (half : F) (w : Nat → F) :
    sourceGather half w 122 = half^0*w 123 := by
  rw [sourceGather_powers, loop122]
  simp <;> ring
#print axioms gather122

lemma gather123 (half : F) (w : Nat → F) :
    sourceGather half w 123 = half*w 122 + half^2*w 120 + half^2*w 124 := by
  rw [sourceGather_powers, loop123]
  simp <;> ring
#print axioms gather123

lemma gather124 (half : F) (w : Nat → F) :
    sourceGather half w 124 = half^0*w 125 := by
  rw [sourceGather_powers, loop124]
  simp <;> ring
#print axioms gather124

lemma gather125 (half : F) (w : Nat → F) :
    sourceGather half w 125 = half*w 124 + half*w 126 := by
  rw [sourceGather_powers, loop125]
  simp <;> ring
#print axioms gather125

lemma gather126 (half : F) (w : Nat → F) :
    sourceGather half w 126 = half^0*w 127 := by
  rw [sourceGather_powers, loop126]
  simp <;> ring
#print axioms gather126

lemma gather127 (half : F) (w : Nat → F) :
    sourceGather half w 127 = half*w 126 + half^2*w 124 + half^3*w 120 + half^4*w 112 + half^5*w 96 + half^6*w 64 + half^7*w 0 + half^7*w 128 := by
  rw [sourceGather_powers, loop127]
  simp <;> ring
#print axioms gather127

lemma gather129 (half : F) (w : Nat → F) :
    sourceGather half w 129 = half*w 128 + half*w 130 := by
  rw [sourceGather_powers, loop129]
  simp <;> ring
#print axioms gather129

lemma gather130 (half : F) (w : Nat → F) :
    sourceGather half w 130 = half^0*w 131 := by
  rw [sourceGather_powers, loop130]
  simp <;> ring
#print axioms gather130

lemma gather131 (half : F) (w : Nat → F) :
    sourceGather half w 131 = half*w 130 + half^2*w 128 + half^2*w 132 := by
  rw [sourceGather_powers, loop131]
  simp <;> ring
#print axioms gather131

lemma gather132 (half : F) (w : Nat → F) :
    sourceGather half w 132 = half^0*w 133 := by
  rw [sourceGather_powers, loop132]
  simp <;> ring
#print axioms gather132

lemma gather133 (half : F) (w : Nat → F) :
    sourceGather half w 133 = half*w 132 + half*w 134 := by
  rw [sourceGather_powers, loop133]
  simp <;> ring
#print axioms gather133

lemma gather134 (half : F) (w : Nat → F) :
    sourceGather half w 134 = half^0*w 135 := by
  rw [sourceGather_powers, loop134]
  simp <;> ring
#print axioms gather134

lemma gather135 (half : F) (w : Nat → F) :
    sourceGather half w 135 = half*w 134 + half^2*w 132 + half^3*w 128 + half^3*w 136 := by
  rw [sourceGather_powers, loop135]
  simp <;> ring
#print axioms gather135

lemma gather136 (half : F) (w : Nat → F) :
    sourceGather half w 136 = half^0*w 137 := by
  rw [sourceGather_powers, loop136]
  simp <;> ring
#print axioms gather136

lemma gather137 (half : F) (w : Nat → F) :
    sourceGather half w 137 = half*w 136 + half*w 138 := by
  rw [sourceGather_powers, loop137]
  simp <;> ring
#print axioms gather137

lemma gather138 (half : F) (w : Nat → F) :
    sourceGather half w 138 = half^0*w 139 := by
  rw [sourceGather_powers, loop138]
  simp <;> ring
#print axioms gather138

lemma gather139 (half : F) (w : Nat → F) :
    sourceGather half w 139 = half*w 138 + half^2*w 136 + half^2*w 140 := by
  rw [sourceGather_powers, loop139]
  simp <;> ring
#print axioms gather139

lemma gather140 (half : F) (w : Nat → F) :
    sourceGather half w 140 = half^0*w 141 := by
  rw [sourceGather_powers, loop140]
  simp <;> ring
#print axioms gather140

lemma gather141 (half : F) (w : Nat → F) :
    sourceGather half w 141 = half*w 140 + half*w 142 := by
  rw [sourceGather_powers, loop141]
  simp <;> ring
#print axioms gather141

lemma gather142 (half : F) (w : Nat → F) :
    sourceGather half w 142 = half^0*w 143 := by
  rw [sourceGather_powers, loop142]
  simp <;> ring
#print axioms gather142

lemma gather143 (half : F) (w : Nat → F) :
    sourceGather half w 143 = half*w 142 + half^2*w 140 + half^3*w 136 + half^4*w 128 + half^4*w 144 := by
  rw [sourceGather_powers, loop143]
  simp <;> ring
#print axioms gather143

lemma gather144 (half : F) (w : Nat → F) :
    sourceGather half w 144 = half^0*w 145 := by
  rw [sourceGather_powers, loop144]
  simp <;> ring
#print axioms gather144

lemma gather145 (half : F) (w : Nat → F) :
    sourceGather half w 145 = half*w 144 + half*w 146 := by
  rw [sourceGather_powers, loop145]
  simp <;> ring
#print axioms gather145

lemma gather146 (half : F) (w : Nat → F) :
    sourceGather half w 146 = half^0*w 147 := by
  rw [sourceGather_powers, loop146]
  simp <;> ring
#print axioms gather146

lemma gather147 (half : F) (w : Nat → F) :
    sourceGather half w 147 = half*w 146 + half^2*w 144 + half^2*w 148 := by
  rw [sourceGather_powers, loop147]
  simp <;> ring
#print axioms gather147

lemma gather148 (half : F) (w : Nat → F) :
    sourceGather half w 148 = half^0*w 149 := by
  rw [sourceGather_powers, loop148]
  simp <;> ring
#print axioms gather148
end AspisV8R19.R748GatherExpand02
