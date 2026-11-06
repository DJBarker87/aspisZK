import NLF_SdkModel
set_option autoImplicit false
namespace NLF_SdkModel
open NLF_RefCell

theorem shared_result (s : State) (i t : Nat)
    (free : (s.cells i).writer = none) (fresh : t ∉ (s.cells i).readers)
    (bound : (s.cells i).readers.length < 9223372036854775807) :
    wrap s i t .shared =
      (put s i {s.cells i with readers := t :: (s.cells i).readers}, .ok ⟨i,t,.shared⟩) := by
  simp [wrap, shared, free, fresh, bound]

theorem exclusive_result (s : State) (i t : Nat)
    (free : (s.cells i).writer = none) (empty : (s.cells i).readers = []) :
    wrap s i t .exclusive =
      (put s i {s.cells i with writer := some t}, .ok ⟨i,t,.exclusive⟩) := by
  simp [wrap, exclusive, free, empty]

theorem shared_deref (s : State) (i t : Nat) :
    deref (put s i {s.cells i with readers := t :: (s.cells i).readers}) ⟨i,t,.shared⟩ =
      (s.cells i).payload := by simp [deref, put]

theorem exclusive_deref (s : State) (i t : Nat) :
    deref (put s i {s.cells i with writer := some t}) ⟨i,t,.exclusive⟩ =
      (s.cells i).payload := by simp [deref, put]

theorem shared_release (s : State) (i t : Nat)
    (free : (s.cells i).writer = none) :
    release (put s i {s.cells i with readers := t :: (s.cells i).readers}) ⟨i,t,.shared⟩ =
      .ok s := by
  simp only [release, put_same]
  have h := shared_drop_roundtrip (s.cells i) t
  have hh : dropShared {s.cells i with readers := t :: (s.cells i).readers} t = .ok (s.cells i) := by
    cases hc : s.cells i with
    | mk p r w => simp_all [dropShared]
  rw [hh]
  exact congrArg Except.ok (put_restore s i _)

theorem exclusive_release (s : State) (i t : Nat)
    (free : (s.cells i).writer = none) :
    release (put s i {s.cells i with writer := some t}) ⟨i,t,.exclusive⟩ = .ok s := by
  simp only [release, put_same]
  rw [exclusive_drop_roundtrip (s.cells i) t free]
  exact congrArg Except.ok (put_restore s i _)

theorem scalar_result (s : State) (i t : Nat) (f : Payload → Nat)
    (free : (s.cells i).writer = none) (fresh : t ∉ (s.cells i).readers)
    (bound : (s.cells i).readers.length < 9223372036854775807) :
    scalar s i t f = (s,.ok (f (s.cells i).payload)) := by
  unfold scalar
  rw [shared_result s i t free fresh bound]
  simp only [shared_release s i t free, shared_deref]

#print axioms shared_result
#print axioms exclusive_result
#print axioms shared_deref
#print axioms exclusive_deref
#print axioms shared_release
#print axioms exclusive_release
#print axioms scalar_result
end NLF_SdkModel
