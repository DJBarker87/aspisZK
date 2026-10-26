import RPz7_DrvC_Implementation
set_option autoImplicit false
noncomputable section
namespace AspisR1.DrvC_CurrentSlots
open Aeneas Aeneas.Std Result
open DrvC_Installation DrvC_Carriers Tx1Q_Carriers

theorem current_base {F C : Type} (c : Configuration F C) : current c =
    Op5T_Concrete.current
      {GExp_FirstPair.base c.currentBase c.reserved c.query c.geometry with op16 := Tx1Q_Install.writer} := by
  cases c with
  | mk adapter currentBase stageBase finish reserved query geometry boundaries std =>
    cases currentBase
    rfl

theorem arr_roundtrip {A B : Type} {n : Usize} (f : A → B) (g : B → A)
    (inv : ∀ a, g (f a) = a) (a : Array A n) : arr g (arr f a) = a := by
  cases a
  simp [arr,List.map_map,Function.comp_def,inv]

theorem slice_roundtrip {A B : Type} (f : A → B) (g : B → A)
    (inv : ∀ a, g (f a) = a) (a : Slice A) : slice g (slice f a) = a := by
  cases a
  simp [slice,List.map_map,Function.comp_def,inv]

theorem arr_repeat {A B : Type} (f : A → B) (n : Usize) (a : A) :
    arr f (Array.repeat n a) = Array.repeat n (f a) := by
  apply Subtype.ext
  simp only [arr,Array.repeat,List.map_replicate]

theorem reply_ok {A B : Type} (f : A → B) (a : A) :
    DrvC_Dictionary.reply f (.Ok a) = .Ok (f a) := rfl

#print axioms current_base
#print axioms arr_roundtrip
#print axioms slice_roundtrip
#print axioms arr_repeat
#print axioms reply_ok
end AspisR1.DrvC_CurrentSlots
end
