import S2NativeStepFootprintsV1
set_option autoImplicit false
namespace AspisS2NativeTailAccountViews
open AspisS2NativeStepFootprints

def Separate (a na b nb : Nat) : Prop := a + na ≤ b ∨ b + nb ≤ a

theorem separate_spans (a na b nb : Nat) (h : Separate a na b nb) :
    ∀ address, Span a na address → ¬ Span b nb address := by
  intro address valid conflict
  unfold Separate at h
  unfold Span at valid conflict
  omega

def DataSize (root : Fin 3) : Nat :=
  if root.val=0 then 58295 else if root.val=1 then 1880 else 1768

def Counters (counter : Fin 3 → Nat) (address : Nat) : Prop :=
  ∃ root, Span (counter root) 8 address

/-- Use the actual source probes' finite interval inequalities. No concrete
buffer is normalized and no SDK/guard carrier is replaced. -/
theorem counters_outside_view (counter : Fin 3 → Nat) (base size : Nat)
    (geometry : ∀ root, Separate (counter root) 8 base size) :
    ∀ address, Span base size address → ¬ Counters counter address := by
  intro address valid inside
  obtain ⟨root,flag⟩ := inside
  exact separate_spans _ _ _ _ (geometry root) address flag valid

/-- Copy/cleanup source-step rule for the THREE actual data views. Native
copy and direct cleanup frames, plus the actual SDK range-binding checks,
instantiate these premises externally; this is not a native whole-caller
or runtime correspondence theorem by itself. -/
theorem data_views_after_copy_cleanup {Byte : Type}
    (before copied out : Heap Byte) (data counter : Fin 3 → Nat)
    (checkpoint : Fin 1768 → Byte)
    (copy : Frame before copied (Span (data 2) 1768))
    (cleanup : Frame copied out (Counters counter))
    (counterGeometry : ∀ c d, Separate (counter c) 8 (data d) (DataSize d))
    (copyGeometry : ∀ d, d ≠ 2 → Separate (data 2) 1768 (data d) (DataSize d))
    (saved : View copied (data 2) 1768=checkpoint) :
    (∀ d, d ≠ 2 → View out (data d) (DataSize d)=View before (data d) (DataSize d)) ∧
    View out (data 2) 1768=checkpoint := by
  constructor
  · intro d other
    apply copy_cleanup_other_view before copied out _ _ (data d) (DataSize d) copy cleanup
    intro address valid
    constructor
    · intro inside
      exact separate_spans _ _ _ _ (copyGeometry d other) address inside valid
    · exact counters_outside_view counter _ _ (fun c => counterGeometry c d) address valid
  · apply copy_cleanup_saved_view copied out _ _ _ checkpoint saved cleanup
    exact counters_outside_view counter _ _ (fun c => by
      simpa [DataSize] using counterGeometry c 2)

/-- The protected ranges are the actual descriptor, Rc header, lamports,
amount, key/owner and AccountInfo-container views checked by the Rust binder.
The index type may include extra protected ranges without changing the proof. -/
theorem protected_views_after_copy_cleanup {Byte Index : Type}
    (before copied out : Heap Byte) (checkpoint : Nat) (counter : Fin 3 → Nat)
    (base size : Index → Nat)
    (copy : Frame before copied (Span checkpoint 1768))
    (cleanup : Frame copied out (Counters counter))
    (copyGeometry : ∀ i, Separate checkpoint 1768 (base i) (size i))
    (counterGeometry : ∀ c i, Separate (counter c) 8 (base i) (size i)) :
    ∀ i, View out (base i) (size i)=View before (base i) (size i) := by
  intro i
  apply copy_cleanup_other_view before copied out _ _ (base i) (size i) copy cleanup
  intro address valid
  constructor
  · intro inside
    exact separate_spans _ _ _ _ (copyGeometry i) address inside valid
  · exact counters_outside_view counter _ _ (fun c => counterGeometry c i) address valid

#print axioms separate_spans
#print axioms counters_outside_view
#print axioms data_views_after_copy_cleanup
#print axioms protected_views_after_copy_cleanup
end AspisS2NativeTailAccountViews
