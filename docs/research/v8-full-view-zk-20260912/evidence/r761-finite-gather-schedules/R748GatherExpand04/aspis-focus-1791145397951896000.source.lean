import AspisV8R19.R748GatherExpand03
/-! Generated sourceGather expansions from named ten-fuel schedules. -/
set_option autoImplicit false
namespace AspisV8R19.R748GatherExpand04
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
variable {F : Type*} [CommRing F]
lemma gather181 (half : F) (w : Nat → F) :
    sourceGather half w 181 = half*w 180 + half*w 182 := by
  rw [sourceGather_powers, loop181]
  simp <;> ring
#print axioms gather181

lemma gather182 (half : F) (w : Nat → F) :
    sourceGather half w 182 = half^0*w 183 := by
  rw [sourceGather_powers, loop182]
  simp <;> ring
#print axioms gather182

lemma gather183 (half : F) (w : Nat → F) :
    sourceGather half w 183 = half*w 182 + half^2*w 180 + half^3*w 176 + half^3*w 184 := by
  rw [sourceGather_powers, loop183]
  simp <;> ring
#print axioms gather183

lemma gather184 (half : F) (w : Nat → F) :
    sourceGather half w 184 = half^0*w 185 := by
  rw [sourceGather_powers, loop184]
  simp <;> ring
#print axioms gather184

lemma gather185 (half : F) (w : Nat → F) :
    sourceGather half w 185 = half*w 184 + half*w 186 := by
  rw [sourceGather_powers, loop185]
  simp <;> ring
#print axioms gather185

lemma gather186 (half : F) (w : Nat → F) :
    sourceGather half w 186 = half^0*w 187 := by
  rw [sourceGather_powers, loop186]
  simp <;> ring
#print axioms gather186

lemma gather187 (half : F) (w : Nat → F) :
    sourceGather half w 187 = half*w 186 + half^2*w 184 + half^2*w 188 := by
  rw [sourceGather_powers, loop187]
  simp <;> ring
#print axioms gather187

lemma gather188 (half : F) (w : Nat → F) :
    sourceGather half w 188 = half^0*w 189 := by
  rw [sourceGather_powers, loop188]
  simp <;> ring
#print axioms gather188

lemma gather189 (half : F) (w : Nat → F) :
    sourceGather half w 189 = half*w 188 + half*w 190 := by
  rw [sourceGather_powers, loop189]
  simp <;> ring
#print axioms gather189

lemma gather190 (half : F) (w : Nat → F) :
    sourceGather half w 190 = half^0*w 191 := by
  rw [sourceGather_powers, loop190]
  simp <;> ring
#print axioms gather190

lemma gather191 (half : F) (w : Nat → F) :
    sourceGather half w 191 = half*w 190 + half^2*w 188 + half^3*w 184 + half^4*w 176 + half^5*w 160 + half^6*w 128 + half^6*w 192 := by
  rw [sourceGather_powers, loop191]
  simp <;> ring
#print axioms gather191

lemma gather249 (half : F) (w : Nat → F) :
    sourceGather half w 249 = half*w 248 + half*w 250 := by
  rw [sourceGather_powers, loop249]
  simp <;> ring
#print axioms gather249

lemma gather250 (half : F) (w : Nat → F) :
    sourceGather half w 250 = half^0*w 251 := by
  rw [sourceGather_powers, loop250]
  simp <;> ring
#print axioms gather250

lemma gather251 (half : F) (w : Nat → F) :
    sourceGather half w 251 = half*w 250 + half^2*w 248 + half^2*w 252 := by
  rw [sourceGather_powers, loop251]
  simp <;> ring
#print axioms gather251

lemma gather253 (half : F) (w : Nat → F) :
    sourceGather half w 253 = half*w 252 + half*w 254 := by
  rw [sourceGather_powers, loop253]
  simp <;> ring
#print axioms gather253

lemma gather288 (half : F) (w : Nat → F) :
    sourceGather half w 288 = half^0*w 289 := by
  rw [sourceGather_powers, loop288]
  simp <;> ring
#print axioms gather288

lemma gather304 (half : F) (w : Nat → F) :
    sourceGather half w 304 = half^0*w 305 := by
  rw [sourceGather_powers, loop304]
  simp <;> ring
#print axioms gather304

lemma gather312 (half : F) (w : Nat → F) :
    sourceGather half w 312 = half^0*w 313 := by
  rw [sourceGather_powers, loop312]
  simp <;> ring
#print axioms gather312

lemma gather313 (half : F) (w : Nat → F) :
    sourceGather half w 313 = half*w 312 + half*w 314 := by
  rw [sourceGather_powers, loop313]
  simp <;> ring
#print axioms gather313

lemma gather314 (half : F) (w : Nat → F) :
    sourceGather half w 314 = half^0*w 315 := by
  rw [sourceGather_powers, loop314]
  simp <;> ring
#print axioms gather314

lemma gather315 (half : F) (w : Nat → F) :
    sourceGather half w 315 = half*w 314 + half^2*w 312 + half^2*w 316 := by
  rw [sourceGather_powers, loop315]
  simp <;> ring
#print axioms gather315

lemma gather316 (half : F) (w : Nat → F) :
    sourceGather half w 316 = half^0*w 317 := by
  rw [sourceGather_powers, loop316]
  simp <;> ring
#print axioms gather316

lemma gather317 (half : F) (w : Nat → F) :
    sourceGather half w 317 = half*w 316 + half*w 318 := by
  rw [sourceGather_powers, loop317]
  simp <;> ring
#print axioms gather317

lemma gather318 (half : F) (w : Nat → F) :
    sourceGather half w 318 = half^0*w 319 := by
  rw [sourceGather_powers, loop318]
  simp <;> ring
#print axioms gather318

lemma gather319 (half : F) (w : Nat → F) :
    sourceGather half w 319 = half*w 318 + half^2*w 316 + half^3*w 312 + half^4*w 304 + half^5*w 288 + half^6*w 256 + half^6*w 320 := by
  rw [sourceGather_powers, loop319]
  simp <;> ring
#print axioms gather319

lemma gather320 (half : F) (w : Nat → F) :
    sourceGather half w 320 = half^0*w 321 := by
  rw [sourceGather_powers, loop320]
  simp <;> ring
#print axioms gather320

lemma gather376 (half : F) (w : Nat → F) :
    sourceGather half w 376 = half^0*w 377 := by
  rw [sourceGather_powers, loop376]
  simp <;> ring
#print axioms gather376

lemma gather377 (half : F) (w : Nat → F) :
    sourceGather half w 377 = half*w 376 + half*w 378 := by
  rw [sourceGather_powers, loop377]
  simp <;> ring
#print axioms gather377

lemma gather378 (half : F) (w : Nat → F) :
    sourceGather half w 378 = half^0*w 379 := by
  rw [sourceGather_powers, loop378]
  simp <;> ring
#print axioms gather378

lemma gather379 (half : F) (w : Nat → F) :
    sourceGather half w 379 = half*w 378 + half^2*w 376 + half^2*w 380 := by
  rw [sourceGather_powers, loop379]
  simp <;> ring
#print axioms gather379

lemma gather380 (half : F) (w : Nat → F) :
    sourceGather half w 380 = half^0*w 381 := by
  rw [sourceGather_powers, loop380]
  simp <;> ring
#print axioms gather380

lemma gather381 (half : F) (w : Nat → F) :
    sourceGather half w 381 = half*w 380 + half*w 382 := by
  rw [sourceGather_powers, loop381]
  simp <;> ring
#print axioms gather381
end AspisV8R19.R748GatherExpand04
