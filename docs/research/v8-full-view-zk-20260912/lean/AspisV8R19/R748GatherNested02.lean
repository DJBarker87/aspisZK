import AspisV8R19.R748GatherNested01
/-! Generated nested sourceGather expansions for odd pointWeight indices. -/
set_option autoImplicit false
namespace AspisV8R19.R748GatherNested02
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
open AspisV8R19.R748GatherExpand00
open AspisV8R19.R748GatherExpand01
variable {F : Type*} [CommRing F]
lemma gatherGather150 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 150 = half*w 150 + half^2*w 148 + half^3*w 144 + half^3*w 152 := by
  rw [gather150, gather151] <;> simp <;> ring
#print axioms gatherGather150

lemma gatherGather151 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 151 = half*w 151 + half^2*w 149 + half^3*w 145 + half^3*w 153 := by
  rw [gather151, gather144, gather148, gather150, gather152] <;> simp <;> ring
#print axioms gatherGather151

lemma gatherGather152 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 152 = half*w 152 + half*w 154 := by
  rw [gather152, gather153] <;> simp <;> ring
#print axioms gatherGather152

lemma gatherGather153 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 153 = half*w 153 + half*w 155 := by
  rw [gather153, gather152, gather154] <;> simp <;> ring
#print axioms gatherGather153

lemma gatherGather155 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 155 = half*w 155 + half^2*w 153 + half^2*w 157 := by
  rw [gather155, gather152, gather154, gather156] <;> simp <;> ring
#print axioms gatherGather155

lemma gatherGather156 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 156 = half*w 156 + half*w 158 := by
  rw [gather156, gather157] <;> simp <;> ring
#print axioms gatherGather156

lemma gatherGather157 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 157 = half*w 157 + half*w 159 := by
  rw [gather157, gather156, gather158] <;> simp <;> ring
#print axioms gatherGather157

lemma gatherGather158 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 158 = half*w 158 + half^2*w 156 + half^3*w 152 + half^4*w 144 + half^5*w 128 + half^5*w 160 := by
  rw [gather158, gather159] <;> simp <;> ring
#print axioms gatherGather158

lemma gatherGather159 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 159 = half*w 159 + half^2*w 157 + half^3*w 153 + half^4*w 145 + half^5*w 129 + half^5*w 161 := by
  rw [gather159, gather128, gather144, gather152, gather156, gather158, gather160] <;> simp <;> ring
#print axioms gatherGather159

lemma gatherGather160 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 160 = half*w 160 + half*w 162 := by
  rw [gather160, gather161] <;> simp <;> ring
#print axioms gatherGather160

lemma gatherGather161 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 161 = half*w 161 + half*w 163 := by
  rw [gather161, gather160, gather162] <;> simp <;> ring
#print axioms gatherGather161

lemma gatherGather162 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 162 = half*w 162 + half^2*w 160 + half^2*w 164 := by
  rw [gather162, gather163] <;> simp <;> ring
#print axioms gatherGather162

lemma gatherGather163 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 163 = half*w 163 + half^2*w 161 + half^2*w 165 := by
  rw [gather163, gather160, gather162, gather164] <;> simp <;> ring
#print axioms gatherGather163

lemma gatherGather164 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 164 = half*w 164 + half*w 166 := by
  rw [gather164, gather165] <;> simp <;> ring
#print axioms gatherGather164

lemma gatherGather165 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 165 = half*w 165 + half*w 167 := by
  rw [gather165, gather164, gather166] <;> simp <;> ring
#print axioms gatherGather165

lemma gatherGather166 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 166 = half*w 166 + half^2*w 164 + half^3*w 160 + half^3*w 168 := by
  rw [gather166, gather167] <;> simp <;> ring
#print axioms gatherGather166

lemma gatherGather167 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 167 = half*w 167 + half^2*w 165 + half^3*w 161 + half^3*w 169 := by
  rw [gather167, gather160, gather164, gather166, gather168] <;> simp <;> ring
#print axioms gatherGather167

lemma gatherGather168 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 168 = half*w 168 + half*w 170 := by
  rw [gather168, gather169] <;> simp <;> ring
#print axioms gatherGather168

lemma gatherGather169 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 169 = half*w 169 + half*w 171 := by
  rw [gather169, gather168, gather170] <;> simp <;> ring
#print axioms gatherGather169

lemma gatherGather170 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 170 = half*w 170 + half^2*w 168 + half^2*w 172 := by
  rw [gather170, gather171] <;> simp <;> ring
#print axioms gatherGather170

lemma gatherGather171 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 171 = half*w 171 + half^2*w 169 + half^2*w 173 := by
  rw [gather171, gather168, gather170, gather172] <;> simp <;> ring
#print axioms gatherGather171

lemma gatherGather172 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 172 = half*w 172 + half*w 174 := by
  rw [gather172, gather173] <;> simp <;> ring
#print axioms gatherGather172

lemma gatherGather173 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 173 = half*w 173 + half*w 175 := by
  rw [gather173, gather172, gather174] <;> simp <;> ring
#print axioms gatherGather173

lemma gatherGather174 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 174 = half*w 174 + half^2*w 172 + half^3*w 168 + half^4*w 160 + half^4*w 176 := by
  rw [gather174, gather175] <;> simp <;> ring
#print axioms gatherGather174

lemma gatherGather175 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 175 = half*w 175 + half^2*w 173 + half^3*w 169 + half^4*w 161 + half^4*w 177 := by
  rw [gather175, gather160, gather168, gather172, gather174, gather176] <;> simp <;> ring
#print axioms gatherGather175

lemma gatherGather176 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 176 = half*w 176 + half*w 178 := by
  rw [gather176, gather177] <;> simp <;> ring
#print axioms gatherGather176

lemma gatherGather177 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 177 = half*w 177 + half*w 179 := by
  rw [gather177, gather176, gather178] <;> simp <;> ring
#print axioms gatherGather177

lemma gatherGather178 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 178 = half*w 178 + half^2*w 176 + half^2*w 180 := by
  rw [gather178, gather179] <;> simp <;> ring
#print axioms gatherGather178

lemma gatherGather179 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 179 = half*w 179 + half^2*w 177 + half^2*w 181 := by
  rw [gather179, gather176, gather178, gather180] <;> simp <;> ring
#print axioms gatherGather179

lemma gatherGather180 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 180 = half*w 180 + half*w 182 := by
  rw [gather180, gather181] <;> simp <;> ring
#print axioms gatherGather180

lemma gatherGather182 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 182 = half*w 182 + half^2*w 180 + half^3*w 176 + half^3*w 184 := by
  rw [gather182, gather183] <;> simp <;> ring
#print axioms gatherGather182

lemma gatherGather183 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 183 = half*w 183 + half^2*w 181 + half^3*w 177 + half^3*w 185 := by
  rw [gather183, gather176, gather180, gather182, gather184] <;> simp <;> ring
#print axioms gatherGather183
end AspisV8R19.R748GatherNested02
