import AspisV8R19.SourceChordEvaluation
import AspisV8R19.SourceMaskTransport

/-! Interleave the actual chord lanes and justify the retained 1024 entries.
This is an algebraic evaluator bridge, not extraction of Rust field operations. -/
namespace AspisR19.SourceEncodedOpening
open AspisV8R16 AspisV8R17 AspisCircleTensorBinding HighRepairInvariant
open NormalizedGCore SourceMaskTransport SourceChordEvaluation T163SourceTable
noncomputable section
variable {F : Type*} [Field F] [NeZero (2 : F)]

def circleWeight (x y : F) (r : Nat) : F :=
  naturalLineValue x (r/2) * if r%2=0 then 1 else y

def serialized (n : Nat) (v : Nat → F) (x y : F) : F :=
  ∑ r ∈ Finset.range n, circleWeight x y r*v r

theorem serialized_pairs (n : Nat) (v : Nat → F) (x y : F) :
    serialized (2*n) v x y =
      rangeDot n (naturalLineValue x) (fun i => v (2*i)) +
      y*rangeDot n (naturalLineValue x) (fun i => v (2*i+1)) := by
  induction n with
  | zero => simp [serialized,rangeDot]
  | succ n ih =>
    simp only [serialized,rangeDot] at ih ⊢
    rw [show 2*(n+1)=2*n+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,ih]
    simp only [Finset.sum_range_succ,circleWeight,
      show (2*n)/2=n by omega,show (2*n+1)/2=n by omega,
      show (2*n)%2=0 by omega,show (2*n+1)%2=1 by omega,
      show ¬(1:Nat)=0 by decide,↓reduceIte,mul_one]
    ring

theorem serialized_restrict (m n : Nat) (hmn : m≤n) (v : Nat → F)
    (tail : ∀ r, m≤r → r<n → v r=0) (x y : F) :
    serialized m v x y=serialized n v x y := by
  unfold serialized
  apply Finset.sum_subset (Finset.range_mono hmn)
  intro r hr hnot
  rw [tail r (by simpa only [Finset.mem_range,not_lt] using hnot) (Finset.mem_range.mp hr),mul_zero]

theorem serialized_chord (q : Nat → F) (a b c x y : F) :
    serialized 1028 (sourceChord (2:F)⁻¹ q a b c) x y=outputValue q a b c x y := by
  rw [show 1028=2*514 by decide,serialized_pairs]
  have de (i : Nat) : (2*i)/2=i := by omega
  have do' (i : Nat) : (2*i+1)/2=i := by omega
  have me (i : Nat) : (2*i)%2=0 := by omega
  have mo (i : Nat) : (2*i+1)%2=1 := by omega
  simp only [sourceChord,finiteChordCoefficient,de,do',me,mo,
    show ¬(1:Nat)=0 by decide,↓reduceIte,outputValue,rangeDot,Finset.mul_sum,mul_assoc]

theorem flattened_chord_tail (q : Index 32 → F) (a b c : F) (r : Nat) (hr : 131≤r) :
    sourceChord (2:F)⁻¹ (flatten q) a b c r=0 := by
  apply HighQueryGCore.sourceChord_support _ _ 64 _ _ _ _ _ (by omega)
  intro i hi
  simp [flatten,show ¬i<128 by omega]

theorem retained_chord_evaluation (q : Index 32 → F) (a b c x y : F)
    (circle : x^2+y^2=1) :
    serialized 1024 (sourceChord (2:F)⁻¹ (flatten q) a b c) x y=
      (a+b*x+c*y)*inputValue (flatten q) x y := by
  rw [serialized_restrict 1024 1028 (by decide) _
    (fun r hr _ => flattened_chord_tail q a b c r (by omega)),serialized_chord]
  exact chord_evaluation _ _ _ _ _ _ circle

def encodedOpening (m : Fin 1024 → F) (x y : F) : F :=
  serialized 1024 (fun r => if h : r<1024 then transport inactive 1023 order m ⟨r,h⟩ else 0) x y

theorem mask_opening (q : Index 32 → F) (a b c x y : F) (circle : x^2+y^2=1) :
    encodedOpening (mask (2:F)⁻¹ a b c q) x y=
      (a+b*x+c*y)*inputValue (flatten q) x y := by
  rw [encodedOpening,mask_transport]
  have h : serialized 1024
      (fun r => if hr : r<1024 then code (2:F)⁻¹ a b c q ⟨r,hr⟩ else 0) x y=
      serialized 1024 (sourceChord (2:F)⁻¹ (flatten q) a b c) x y := by
    unfold serialized
    apply Finset.sum_congr rfl
    intro r hr
    simp only [dif_pos (Finset.mem_range.mp hr),code]
  rw [h]
  exact retained_chord_evaluation q a b c x y circle

theorem mask_first_ood_zero (q : Index 32 → F) (x0 y0 x1 y1 : F)
    (circle : x0^2+y0^2=1) :
    encodedOpening (mask (2:F)⁻¹ (x0*y1-y0*x1) (y0-y1) (x1-x0) q) x0 y0=0 := by
  rw [mask_opening q _ _ _ x0 y0 circle]
  have h : x0*y1-y0*x1+(y0-y1)*x0+(x1-x0)*y0=0 := by ring
  rw [h,zero_mul]

theorem mask_second_ood_zero (q : Index 32 → F) (x0 y0 x1 y1 : F)
    (circle : x1^2+y1^2=1) :
    encodedOpening (mask (2:F)⁻¹ (x0*y1-y0*x1) (y0-y1) (x1-x0) q) x1 y1=0 := by
  rw [mask_opening q _ _ _ x1 y1 circle]
  have h : x0*y1-y0*x1+(y0-y1)*x1+(x1-x0)*y1=0 := by ring
  rw [h,zero_mul]

#print axioms serialized_pairs
#print axioms serialized_restrict
#print axioms serialized_chord
#print axioms flattened_chord_tail
#print axioms retained_chord_evaluation
#print axioms mask_opening
#print axioms mask_first_ood_zero
#print axioms mask_second_ood_zero
end
end AspisR19.SourceEncodedOpening
