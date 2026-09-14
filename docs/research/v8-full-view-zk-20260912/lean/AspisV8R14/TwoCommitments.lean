import AspisV8R13.MovingLeaves

/-!
Two chronological payload-dependent commitments in ONE partitioned function.
C2 addresses may depend on the already selected C1 answers. These maps act on
whole experiments, NOT a live oracle. The source partition remains explicit.
DRAFT: not compiled in the packet-building environment.
-/
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8R14
open AspisV8R13
variable {C Index Key Digest : Type*} [DecidableEq Key]
abbrev TwinWorld (C Index Key Digest : Type*) :=
  C × LeafOracle Index Key Digest × LeafOracle Index Key Digest

def normalizeTwo
    (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key)
    (a b : Index → Key) (w : TwinWorld C Index Key Digest) :
    TwinWorld C Index Key Digest :=
  let h := selected w.2.1 (first w.1)
  (w.1, swapFamilies w.2.1 (first w.1) a,
    swapFamilies w.2.2 (second w.1 h) b)

def denormalizeTwo
    (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key)
    (a b : Index → Key) (w : TwinWorld C Index Key Digest) :
    TwinWorld C Index Key Digest :=
  let h := selected w.2.1 a
  (w.1, swapFamilies w.2.1 a (first w.1),
    swapFamilies w.2.2 b (second w.1 h))

theorem normalizeTwo_left_inverse
    (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key) (a b : Index → Key)
    (w : TwinWorld C Index Key Digest) :
    denormalizeTwo first second a b (normalizeTwo first second a b w) = w := by
  rcases w with ⟨c,H1,H2⟩
  simp only [normalizeTwo, denormalizeTwo, selected_swapFamilies,
    swapFamilies_reverse]

theorem normalizeTwo_right_inverse
    (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key) (a b : Index → Key)
    (w : TwinWorld C Index Key Digest) :
    normalizeTwo first second a b (denormalizeTwo first second a b w) = w := by
  rcases w with ⟨c,H1,H2⟩
  simp only [normalizeTwo, denormalizeTwo, selected_swapFamilies,
    swapFamilies_reverse]

def twoCommitmentEquiv
    (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key) (a b : Index → Key) :
    TwinWorld C Index Key Digest ≃ TwinWorld C Index Key Digest where
  toFun := normalizeTwo first second a b
  invFun := denormalizeTwo first second a b
  left_inv := normalizeTwo_left_inverse first second a b
  right_inv := normalizeTwo_right_inverse first second a b

theorem normalizeTwo_first_handle
    (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key) (a b : Index → Key)
    (w : TwinWorld C Index Key Digest) :
    selected (normalizeTwo first second a b w).2.1 a =
      selected w.2.1 (first w.1) := by simp [normalizeTwo]

theorem normalizeTwo_second_handle
    (first : C → Index → Key)
    (second : C → (Index → Digest) → Index → Key) (a b : Index → Key)
    (w : TwinWorld C Index Key Digest) :
    selected (normalizeTwo first second a b w).2.2 b =
      selected w.2.2 (second w.1 (selected w.2.1 (first w.1))) := by
  simp [normalizeTwo]

#print axioms twoCommitmentEquiv
#print axioms normalizeTwo_first_handle
#print axioms normalizeTwo_second_handle
end AspisV8R14
