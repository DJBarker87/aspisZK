import RPt_BEl_GateBounds
set_option autoImplicit false
namespace AspisR1.BEm_PaddingModel

/-- Arithmetic/traversal model of a padding word. This is not an extracted
Rust function, nor an assumption asserting the physical batch association. -/
structure Word where
  b0 : Nat
  b1 : Nat
  b2 : Nat
  b3 : Nat
  b4 : Nat
  b5 : Nat
  b6 : Nat
  b7 : Nat

def bytes (w : Word) : List Nat := [w.b0,w.b1,w.b2,w.b3,w.b4,w.b5,w.b6,w.b7]
def valid (w : Word) : Prop := ∀ b ∈ bytes w, b < 256
def value (w : Word) : Nat := w.b0 + 256*w.b1 + 65536*w.b2 +
  16777216*w.b3 + 4294967296*w.b4 + 1099511627776*w.b5 +
  281474976710656*w.b6 + 72057594037927936*w.b7

theorem zero (w : Word) : value w = 0 ↔ ∀ b ∈ bytes w, b = 0 := by
  constructor
  · intro allZero b member
    unfold value at allZero
    simp only [bytes,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · intro allZero
    have h0 := allZero w.b0 (by simp [bytes])
    have h1 := allZero w.b1 (by simp [bytes])
    have h2 := allZero w.b2 (by simp [bytes])
    have h3 := allZero w.b3 (by simp [bytes])
    have h4 := allZero w.b4 (by simp [bytes])
    have h5 := allZero w.b5 (by simp [bytes])
    have h6 := allZero w.b6 (by simp [bytes])
    have h7 := allZero w.b7 (by simp [bytes])
    simp only [value,h0,h1,h2,h3,h4,h5,h6,h7,Nat.mul_zero,Nat.zero_add]

theorem bound (w : Word) (admitted : valid w) : value w < 18446744073709551616 := by
  simp only [valid,bytes,List.mem_cons,List.not_mem_nil,or_false] at admitted
  have h0 := admitted w.b0 (by tauto)
  have h1 := admitted w.b1 (by tauto)
  have h2 := admitted w.b2 (by tauto)
  have h3 := admitted w.b3 (by tauto)
  have h4 := admitted w.b4 (by tauto)
  have h5 := admitted w.b5 (by tauto)
  have h6 := admitted w.b6 (by tauto)
  have h7 := admitted w.b7 (by tauto)
  unfold value
  omega

def nativeWord (w : Word) : Bool := decide (value w % 18446744073709551616 ≠ 0)
def referenceWord (w : Word) : Bool := (bytes w).any (fun b => decide (b ≠ 0))

theorem word (w : Word) (admitted : valid w) : nativeWord w = referenceWord w := by
  have small := bound w admitted
  apply Bool.eq_iff_iff.mpr
  simp only [nativeWord,Nat.mod_eq_of_lt small,decide_eq_true_eq,referenceWord,List.any_eq_true,
    decide_eq_true_eq]
  have z := zero w
  constructor
  · intro nonzero
    by_contra missing
    apply nonzero
    apply z.mpr
    intro b member
    by_contra different
    exact missing ⟨b,member,different⟩
  · rintro ⟨b,member,different⟩ allZero
    exact different (z.mp allZero b member)

/-- Generic first-loop split: no concrete688-word term is evaluated. -/
theorem traversal (words : List Word) (admitted : ∀ w ∈ words, valid w) :
    words.any nativeWord = (words.flatMap bytes).any (fun b => decide (b ≠ 0)) := by
  induction words with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.any_cons,List.flatMap_cons,List.any_append]
    rw [word w (admitted w (List.mem_cons_self ..))]
    rw [ih (fun w member => admitted w (List.mem_cons_of_mem _ member))]
    rfl

#print axioms zero
#print axioms bound
#print axioms word
#print axioms traversal
end AspisR1.BEm_PaddingModel
