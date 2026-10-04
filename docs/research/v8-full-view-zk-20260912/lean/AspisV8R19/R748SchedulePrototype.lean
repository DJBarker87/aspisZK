import AspisV8R19.R748FiniteGatherSchedules
/-! Prototype only: densest newly required finite gather schedule, before compilation. -/
set_option autoImplicit false
namespace AspisV8R19.R748SchedulePrototype
open AspisV8R17
open AspisV8R19.R742SourceObservationHom
open AspisV8R19.R748FiniteGatherSchedules

lemma loop255 : indexLoop 10 255 0 = some [(254,1),(252,2),(248,3),(240,4),(224,5),(192,6),(128,7),(0,8),(256,8)] := by rfl
#print axioms loop255

variable {F : Type*} [CommRing F]
lemma gather255 (half : F) (w : Nat → F) :
    sourceGather half w 255 = half*w 254 + half^2*w 252 + half^3*w 248 + half^4*w 240 + half^5*w 224 + half^6*w 192 + half^7*w 128 + half^8*w 0 + half^8*w 256 := by
  rw [sourceGather_powers, loop255]
  simp <;> ring
#print axioms gather255


-- Supporting child schedules and expansions required by gatherGather255.
lemma loop254 : indexLoop 10 254 0 = some [(255,0)] := by rfl
#print axioms loop254
lemma gather254 (half : F) (w : Nat → F) :
    sourceGather half w 254 = half^0*w 255 := by
  rw [sourceGather_powers, loop254]
  simp <;> ring
#print axioms gather254
lemma loop252 : indexLoop 10 252 0 = some [(253,0)] := by rfl
#print axioms loop252
lemma gather252 (half : F) (w : Nat → F) :
    sourceGather half w 252 = half^0*w 253 := by
  rw [sourceGather_powers, loop252]
  simp <;> ring
#print axioms gather252
lemma loop248 : indexLoop 10 248 0 = some [(249,0)] := by rfl
#print axioms loop248
lemma gather248 (half : F) (w : Nat → F) :
    sourceGather half w 248 = half^0*w 249 := by
  rw [sourceGather_powers, loop248]
  simp <;> ring
#print axioms gather248
lemma loop240 : indexLoop 10 240 0 = some [(241,0)] := by rfl
#print axioms loop240
lemma gather240 (half : F) (w : Nat → F) :
    sourceGather half w 240 = half^0*w 241 := by
  rw [sourceGather_powers, loop240]
  simp <;> ring
#print axioms gather240
lemma loop224 : indexLoop 10 224 0 = some [(225,0)] := by rfl
#print axioms loop224
lemma gather224 (half : F) (w : Nat → F) :
    sourceGather half w 224 = half^0*w 225 := by
  rw [sourceGather_powers, loop224]
  simp <;> ring
#print axioms gather224
lemma loop192 : indexLoop 10 192 0 = some [(193,0)] := by rfl
#print axioms loop192
lemma gather192 (half : F) (w : Nat → F) :
    sourceGather half w 192 = half^0*w 193 := by
  rw [sourceGather_powers, loop192]
  simp <;> ring
#print axioms gather192
lemma loop128 : indexLoop 10 128 0 = some [(129,0)] := by rfl
#print axioms loop128
lemma gather128 (half : F) (w : Nat → F) :
    sourceGather half w 128 = half^0*w 129 := by
  rw [sourceGather_powers, loop128]
  simp <;> ring
#print axioms gather128
lemma loop256 : indexLoop 10 256 0 = some [(257,0)] := by rfl
#print axioms loop256
lemma gather256 (half : F) (w : Nat → F) :
    sourceGather half w 256 = half^0*w 257 := by
  rw [sourceGather_powers, loop256]
  simp <;> ring
#print axioms gather256

lemma gatherGather255 (half : F) (w : Nat → F) :
    sourceGather half (sourceGather half w) 255 = half*w 255 + half^2*w 253 + half^3*w 249 + half^4*w 241 + half^5*w 225 + half^6*w 193 + half^7*w 129 + half^8*w 1 + half^8*w 257 := by
  rw [gather255, gather254, gather252, gather248, gather240, gather224, gather192, gather128, gather0, gather256]
  simp <;> ring
#print axioms gatherGather255
end AspisV8R19.R748SchedulePrototype
