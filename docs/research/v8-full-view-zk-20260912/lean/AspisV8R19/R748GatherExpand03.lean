import AspisV8R19.R748GatherExpand02
/-! Generated sourceGather expansions from named ten-fuel schedules. -/
set_option autoImplicit false
namespace AspisV8R19.R748GatherExpand03
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
variable {F : Type*} [CommRing F]
lemma gather149 (half : F) (w : Nat → F) :
    sourceGather half w 149 = half*w 148 + half*w 150 := by
  rw [sourceGather_powers, loop149]
  simp <;> ring
#print axioms gather149

lemma gather150 (half : F) (w : Nat → F) :
    sourceGather half w 150 = half^0*w 151 := by
  rw [sourceGather_powers, loop150]
  simp <;> ring
#print axioms gather150

lemma gather151 (half : F) (w : Nat → F) :
    sourceGather half w 151 = half*w 150 + half^2*w 148 + half^3*w 144 + half^3*w 152 := by
  rw [sourceGather_powers, loop151]
  simp <;> ring
#print axioms gather151

lemma gather152 (half : F) (w : Nat → F) :
    sourceGather half w 152 = half^0*w 153 := by
  rw [sourceGather_powers, loop152]
  simp <;> ring
#print axioms gather152

lemma gather153 (half : F) (w : Nat → F) :
    sourceGather half w 153 = half*w 152 + half*w 154 := by
  rw [sourceGather_powers, loop153]
  simp <;> ring
#print axioms gather153

lemma gather154 (half : F) (w : Nat → F) :
    sourceGather half w 154 = half^0*w 155 := by
  rw [sourceGather_powers, loop154]
  simp <;> ring
#print axioms gather154

lemma gather155 (half : F) (w : Nat → F) :
    sourceGather half w 155 = half*w 154 + half^2*w 152 + half^2*w 156 := by
  rw [sourceGather_powers, loop155]
  simp <;> ring
#print axioms gather155

lemma gather156 (half : F) (w : Nat → F) :
    sourceGather half w 156 = half^0*w 157 := by
  rw [sourceGather_powers, loop156]
  simp <;> ring
#print axioms gather156

lemma gather157 (half : F) (w : Nat → F) :
    sourceGather half w 157 = half*w 156 + half*w 158 := by
  rw [sourceGather_powers, loop157]
  simp <;> ring
#print axioms gather157

lemma gather158 (half : F) (w : Nat → F) :
    sourceGather half w 158 = half^0*w 159 := by
  rw [sourceGather_powers, loop158]
  simp <;> ring
#print axioms gather158

lemma gather159 (half : F) (w : Nat → F) :
    sourceGather half w 159 = half*w 158 + half^2*w 156 + half^3*w 152 + half^4*w 144 + half^5*w 128 + half^5*w 160 := by
  rw [sourceGather_powers, loop159]
  simp <;> ring
#print axioms gather159

lemma gather160 (half : F) (w : Nat → F) :
    sourceGather half w 160 = half^0*w 161 := by
  rw [sourceGather_powers, loop160]
  simp <;> ring
#print axioms gather160

lemma gather161 (half : F) (w : Nat → F) :
    sourceGather half w 161 = half*w 160 + half*w 162 := by
  rw [sourceGather_powers, loop161]
  simp <;> ring
#print axioms gather161

lemma gather162 (half : F) (w : Nat → F) :
    sourceGather half w 162 = half^0*w 163 := by
  rw [sourceGather_powers, loop162]
  simp <;> ring
#print axioms gather162

lemma gather163 (half : F) (w : Nat → F) :
    sourceGather half w 163 = half*w 162 + half^2*w 160 + half^2*w 164 := by
  rw [sourceGather_powers, loop163]
  simp <;> ring
#print axioms gather163

lemma gather164 (half : F) (w : Nat → F) :
    sourceGather half w 164 = half^0*w 165 := by
  rw [sourceGather_powers, loop164]
  simp <;> ring
#print axioms gather164

lemma gather165 (half : F) (w : Nat → F) :
    sourceGather half w 165 = half*w 164 + half*w 166 := by
  rw [sourceGather_powers, loop165]
  simp <;> ring
#print axioms gather165

lemma gather166 (half : F) (w : Nat → F) :
    sourceGather half w 166 = half^0*w 167 := by
  rw [sourceGather_powers, loop166]
  simp <;> ring
#print axioms gather166

lemma gather167 (half : F) (w : Nat → F) :
    sourceGather half w 167 = half*w 166 + half^2*w 164 + half^3*w 160 + half^3*w 168 := by
  rw [sourceGather_powers, loop167]
  simp <;> ring
#print axioms gather167

lemma gather168 (half : F) (w : Nat → F) :
    sourceGather half w 168 = half^0*w 169 := by
  rw [sourceGather_powers, loop168]
  simp <;> ring
#print axioms gather168

lemma gather169 (half : F) (w : Nat → F) :
    sourceGather half w 169 = half*w 168 + half*w 170 := by
  rw [sourceGather_powers, loop169]
  simp <;> ring
#print axioms gather169

lemma gather170 (half : F) (w : Nat → F) :
    sourceGather half w 170 = half^0*w 171 := by
  rw [sourceGather_powers, loop170]
  simp <;> ring
#print axioms gather170

lemma gather171 (half : F) (w : Nat → F) :
    sourceGather half w 171 = half*w 170 + half^2*w 168 + half^2*w 172 := by
  rw [sourceGather_powers, loop171]
  simp <;> ring
#print axioms gather171

lemma gather172 (half : F) (w : Nat → F) :
    sourceGather half w 172 = half^0*w 173 := by
  rw [sourceGather_powers, loop172]
  simp <;> ring
#print axioms gather172

lemma gather173 (half : F) (w : Nat → F) :
    sourceGather half w 173 = half*w 172 + half*w 174 := by
  rw [sourceGather_powers, loop173]
  simp <;> ring
#print axioms gather173

lemma gather174 (half : F) (w : Nat → F) :
    sourceGather half w 174 = half^0*w 175 := by
  rw [sourceGather_powers, loop174]
  simp <;> ring
#print axioms gather174

lemma gather175 (half : F) (w : Nat → F) :
    sourceGather half w 175 = half*w 174 + half^2*w 172 + half^3*w 168 + half^4*w 160 + half^4*w 176 := by
  rw [sourceGather_powers, loop175]
  simp <;> ring
#print axioms gather175

lemma gather176 (half : F) (w : Nat → F) :
    sourceGather half w 176 = half^0*w 177 := by
  rw [sourceGather_powers, loop176]
  simp <;> ring
#print axioms gather176

lemma gather177 (half : F) (w : Nat → F) :
    sourceGather half w 177 = half*w 176 + half*w 178 := by
  rw [sourceGather_powers, loop177]
  simp <;> ring
#print axioms gather177

lemma gather178 (half : F) (w : Nat → F) :
    sourceGather half w 178 = half^0*w 179 := by
  rw [sourceGather_powers, loop178]
  simp <;> ring
#print axioms gather178

lemma gather179 (half : F) (w : Nat → F) :
    sourceGather half w 179 = half*w 178 + half^2*w 176 + half^2*w 180 := by
  rw [sourceGather_powers, loop179]
  simp <;> ring
#print axioms gather179

lemma gather180 (half : F) (w : Nat → F) :
    sourceGather half w 180 = half^0*w 181 := by
  rw [sourceGather_powers, loop180]
  simp <;> ring
#print axioms gather180
end AspisV8R19.R748GatherExpand03
