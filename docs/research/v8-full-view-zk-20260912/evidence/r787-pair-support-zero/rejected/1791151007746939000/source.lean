import AspisV8R19.R738JointObservationModel
import AspisV8R19.R773LowActiveKernel

set_option autoImplicit false
namespace AspisV8R19.R787PairSupportZero
open AspisV8R17
open AspisV8R19.R738JointObservationModel
open AspisV8R19.R773LowActiveKernel
noncomputable section
variable {F : Type*} [CommRing F]

def pairSupport (d : Fin 255) (s : Fin 3) (r : Nat) : Prop :=
  evenUnitSupport (2*d.val) r ∨
    (if s.val=1 then evenUnitSupport (2*d.val+1) r
     else oddUnitSupport (2*d.val+s.val/2) r)

theorem qPair_sourceChord_zero_of_not_pairSupport (half alpha a b c : F)
    (d : Fin 255) (s : Fin 3) (r : Nat)
    (h : ¬ pairSupport d s r) :
    sourceChord half (qPair alpha d s) a b c r = 0 := by
  have hdiff := sourceChord_difference half
      (unitVector (4*d.val+s.val+1)) (unitVector (4*d.val))
      a b c (alpha^(s.val+1)) r
  change sourceChord half
      (fun i => unitVector (4*d.val+s.val+1) i -
        alpha^(s.val+1)*unitVector (4*d.val) i) a b c r = 0
  rw [hdiff]
  fin_cases s
  · have hn : ¬ (evenUnitSupport (2*d.val) r ∨ oddUnitSupport (2*d.val) r) := by
      simpa [pairSupport] using h
    have he : ¬ evenUnitSupport (2*d.val) r := fun hs => hn (Or.inl hs)
    have ho : ¬ oddUnitSupport (2*d.val) r := fun hs => hn (Or.inr hs)
    have h1 : sourceChord half (unitVector (2*(2*d.val)+1)) a b c r = 0 :=
      sourceChord_odd_zero half (2*d.val) r (by have := d.isLt; omega) ho a b c
    have h2 : sourceChord half (unitVector (2*(2*d.val))) a b c r = 0 :=
      sourceChord_even_zero half (2*d.val) r (by have := d.isLt; omega) he a b c
    simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (show sourceChord half (unitVector (4*d.val+1)) a b c r -
          alpha^1*sourceChord half (unitVector (4*d.val)) a b c r = 0 by
        rw [h1,h2]
        simp)
  · have hn : ¬ (evenUnitSupport (2*d.val) r ∨ evenUnitSupport (2*d.val+1) r) := by
      simpa [pairSupport] using h
    have he0 : ¬ evenUnitSupport (2*d.val) r := fun hs => hn (Or.inl hs)
    have he1 : ¬ evenUnitSupport (2*d.val+1) r := fun hs => hn (Or.inr hs)
    have h1 : sourceChord half (unitVector (2*(2*d.val+1))) a b c r = 0 :=
      sourceChord_even_zero half (2*d.val+1) r (by have := d.isLt; omega) he1 a b c
    have h2 : sourceChord half (unitVector (2*(2*d.val))) a b c r = 0 :=
      sourceChord_even_zero half (2*d.val) r (by have := d.isLt; omega) he0 a b c
    simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (show sourceChord half (unitVector (4*d.val+2)) a b c r -
          alpha^2*sourceChord half (unitVector (4*d.val)) a b c r = 0 by
        rw [h1,h2]
        simp)
  · have hn : ¬ (evenUnitSupport (2*d.val) r ∨ oddUnitSupport (2*d.val+1) r) := by
      simpa [pairSupport] using h
    have he0 : ¬ evenUnitSupport (2*d.val) r := fun hs => hn (Or.inl hs)
    have ho1 : ¬ oddUnitSupport (2*d.val+1) r := fun hs => hn (Or.inr hs)
    have h1 : sourceChord half (unitVector (2*(2*d.val+1)+1)) a b c r = 0 :=
      sourceChord_odd_zero half (2*d.val+1) r (by have := d.isLt; omega) ho1 a b c
    have h2 : sourceChord half (unitVector (2*(2*d.val))) a b c r = 0 :=
      sourceChord_even_zero half (2*d.val) r (by have := d.isLt; omega) he0 a b c
    simpa [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (show sourceChord half (unitVector (4*d.val+3)) a b c r -
          alpha^3*sourceChord half (unitVector (4*d.val)) a b c r = 0 by
        rw [h1,h2]
        simp)

theorem direction_sourceChord_zero_of_not_pairSupport (half alpha a b c : F)
    (d : Fin 255) (s : Fin 3) (r : Nat) (hr : 96 ≤ r)
    (h : ¬ pairSupport d s r) :
    sourceChord half (direction alpha d s) a b c r = 0 := by
  change sourceChord half
      (fun i => qPair alpha d s i - qPair alpha 0 s i) a b c r = 0
  have hdiff := sourceChord_difference half (qPair alpha d s) (qPair alpha 0 s)
      a b c (1 : F) r
  have hfun : (fun i => qPair alpha d s i - qPair alpha 0 s i) =
      (fun i => qPair alpha d s i - (1 : F)*qPair alpha 0 s i) := by
    funext i
    simp
  rw [hfun, hdiff]
  have hhigh := qPair_sourceChord_zero_of_not_pairSupport half alpha a b c d s r h
  have hlow : sourceChord half (qPair alpha 0 s) a b c r = 0 := by
    exact sourceChord_low_pair_zero half a b c alpha ⟨0, by decide⟩ s r hr
  rw [hhigh, hlow]
  simp

#print axioms qPair_sourceChord_zero_of_not_pairSupport
#print axioms direction_sourceChord_zero_of_not_pairSupport
end
end AspisV8R19.R787PairSupportZero
