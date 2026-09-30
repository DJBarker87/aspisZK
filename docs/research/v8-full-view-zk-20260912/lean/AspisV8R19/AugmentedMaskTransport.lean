import AspisV8R19.AugmentedQuotient
import AspisV8R19.CircleObservationBridge
import AspisV8R17.LegalMaskCoordinates

/-! The augmented direction is supported below quotient coordinate 124.
Its source-shaped chord misses every sparse G coin and the balancing pivot.
The basis permutation is a parameter: no T163-specific source theorem is
silently reused as a theorem for the new two-swap profile. -/
set_option autoImplicit false
namespace AspisR19.AugmentedMaskTransport
open AspisV8R16 AspisV8R17 HighRepairInvariant NormalizedGCore
open AspisCircleTensorBinding SourceEncodedOpening CircleChannelsBridge
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def code (half a b c : F) (q : Index 32 → F) (r : Fin 1024) : F :=
  sourceChord half (flatten q) a b c r.val
def mask (inactive : Finset (Fin 1024)) (order : Equiv.Perm (Fin 1024))
    (half a b c : F) (q : Index 32 → F) : Fin 1024 → F :=
  inverseTransport inactive 1023 order (code half a b c q)

theorem normalized_tail (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) (d : Fin 32) (hd : d.val<31)
    (i : Fin 32) (hi : 31 ≤ i.val) :
    AugmentedQuerySection.normalized t ht noneOne d i=0 := by
  rw [AugmentedQuerySection.normalized_high t ht noneOne d i (by omega)]
  have h : i≠d := by intro he; have := congrArg Fin.val he; omega
  simp [h]

theorem quotient_tail (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) (alpha : F) (d : Fin 32) (hd : d.val<31)
    (s : Fin 4) (r : Nat) (hr : 124≤r) :
    flatten (AugmentedQuotient.quotient t ht noneOne alpha d s) r=0 := by
  unfold flatten
  split
  · simp only [AugmentedQuotient.quotient,AugmentedQuotient.lift]
    rw [normalized_tail t ht noneOne d hd _ (show 31 ≤ r/4 by omega),zero_mul]
  · rfl

theorem code_tail (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) (half alpha a b c : F) (d : Fin 32) (hd : d.val<31)
    (s : Fin 4) (r : Fin 1024) (hr : 127≤r.val) :
    code half a b c (AugmentedQuotient.quotient t ht noneOne alpha d s) r=0 := by
  exact HighQueryGCore.sourceChord_support half _ 62
    (quotient_tail t ht noneOne alpha d hd s) a b c r.val hr

theorem mask_transport (inactive : Finset (Fin 1024)) (hp : (1023:Fin 1024)∈inactive)
    (order : Equiv.Perm (Fin 1024)) (half a b c : F) (q : Index 32 → F) :
    transport inactive 1023 order (mask inactive order half a b c q)=code half a b c q :=
  transport_inverse inactive 1023 hp order _

theorem mask_balanced (inactive : Finset (Fin 1024)) (hp : (1023:Fin 1024)∈inactive)
    (order : Equiv.Perm (Fin 1024)) (fixed : order 1023=1023)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i≠1)
    (half alpha a b c : F) (d : Fin 32) (hd : d.val<31) (s : Fin 4) :
    ∑ r ∈ inactive, mask inactive order half a b c
      (AugmentedQuotient.quotient t ht noneOne alpha d s) r=0 := by
  have h := congrFun (mask_transport inactive hp order half a b c
    (AugmentedQuotient.quotient t ht noneOne alpha d s)) 1023
  simp only [transport,fixed,↓reduceIte] at h
  exact h.trans (code_tail t ht noneOne half alpha a b c d hd s 1023 (by decide))

def coinIndex (i : Fin 271) : Fin 1024 := ⟨128+3*i.val,by omega⟩

theorem mask_coins_zero (inactive : Finset (Fin 1024))
    (order : Equiv.Perm (Fin 1024)) (fixed : order 1023=1023)
    (t : Fin 22 → F) (ht : Function.Injective t) (noneOne : ∀ i, t i≠1)
    (half alpha a b c : F) (d : Fin 32) (hd : d.val<31) (s : Fin 4) (i : Fin 271) :
    mask inactive order half a b c (AugmentedQuotient.quotient t ht noneOne alpha d s)
      (order (coinIndex i))=0 := by
  have hn : order (coinIndex i)≠1023 := by
    intro h
    have he := congrArg Fin.val (order.injective (h.trans fixed.symm))
    have hi:=i.isLt
    simp only [coinIndex,Fin.val_ofNat] at he
    omega
  simp only [mask,inverseTransport,if_neg hn,Equiv.symm_apply_apply]
  exact code_tail t ht noneOne half alpha a b c d hd s _ (by dsimp [coinIndex]; omega)

def opening (inactive : Finset (Fin 1024)) (order : Equiv.Perm (Fin 1024))
    (m : Fin 1024 → F) (x y : F) : F :=
  serialized 1024 (fun r => if h : r<1024 then
    transport inactive 1023 order m ⟨r,h⟩ else 0) x y

theorem mask_opening (inactive : Finset (Fin 1024)) (hp : (1023:Fin 1024)∈inactive)
    (order : Equiv.Perm (Fin 1024)) (q : Index 32 → F) (a b c x y : F)
    (circle : x^2+y^2=1) :
    opening inactive order (mask inactive order (2:F)⁻¹ a b c q) x y=
      (a+b*x+c*y)*SourceChordEvaluation.inputValue (flatten q) x y := by
  rw [opening,mask_transport inactive hp]
  have h : serialized 1024
      (fun r => if hr : r<1024 then code (2:F)⁻¹ a b c q ⟨r,hr⟩ else 0) x y=
      serialized 1024 (sourceChord (2:F)⁻¹ (flatten q) a b c) x y := by
    unfold serialized
    apply Finset.sum_congr rfl
    intro r hr
    simp only [dif_pos (Finset.mem_range.mp hr),code]
  rw [h]
  exact retained_chord_evaluation q a b c x y circle

theorem mask_root_zero (inactive : Finset (Fin 1024)) (hp : (1023:Fin 1024)∈inactive)
    (order : Equiv.Perm (Fin 1024)) (t : Fin 22 → F) (ht : Function.Injective t)
    (noneOne : ∀ i, t i≠1) (alpha : F) (d : Fin 32) (s : Fin 4) (j : Fin 22)
    (a b c x y : F) (circle : x^2+y^2=1) (root : doubledFactor x 1=t j) :
    opening inactive order (mask inactive order (2:F)⁻¹ a b c
      (AugmentedQuotient.quotient t ht noneOne alpha d s)) x y=0 := by
  rw [mask_opening inactive hp order _ a b c x y circle,input_channels]
  simp only [channels,root,AugmentedQuotient.quotient_root]
  ring

#print axioms normalized_tail
#print axioms quotient_tail
#print axioms code_tail
#print axioms mask_transport
#print axioms mask_balanced
#print axioms mask_coins_zero
#print axioms mask_opening
#print axioms mask_root_zero
end
end AspisR19.AugmentedMaskTransport
