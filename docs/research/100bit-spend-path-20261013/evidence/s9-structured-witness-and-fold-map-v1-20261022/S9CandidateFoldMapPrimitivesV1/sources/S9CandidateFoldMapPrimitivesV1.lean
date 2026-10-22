import RangeFoldP6ModelV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CandidateFoldMapPrimitivesV1

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | .ok x => .ok (f x)
  | .fail e => .fail e
  | .div => .div

theorem mapResult_bind {A B C : Type} (f : B → C) (r : Result A)
    (k : A → Result B) :
    (mapResult f (do let x ← r; k x)) = (do let x ← r; mapResult f (k x)) := by
  cases r with
  | fail e => rfl
  | div => rfl
  | ok x => rfl

/-- Bind naturality when the intermediate value itself changes carrier. -/
theorem mapResult_bind_congr {A A' B B' : Type}
    (f : B → B') (g : A → A')
    (r : Result A) (r' : Result A')
    (k : A → Result B) (k' : A' → Result B')
    (hr : mapResult g r = r')
    (hk : ∀ a, mapResult f (k a) = k' (g a)) :
    (mapResult f (do let a ← r; k a)) = (do let a' ← r'; k' a') := by
  cases r with
  | fail e =>
      cases r' with
      | fail e' =>
          have he : e = e' := by simpa [mapResult] using hr
          subst e'
          rfl
      | div => simp [mapResult] at hr
      | ok a' => simp [mapResult] at hr
  | div =>
      cases r' with
      | fail e' => simp [mapResult] at hr
      | div => rfl
      | ok a' => simp [mapResult] at hr
  | ok a =>
      cases r' with
      | fail e' => simp [mapResult] at hr
      | div => simp [mapResult] at hr
      | ok a' =>
          have ha : g a = a' := by simpa [mapResult] using hr
          subst a'
          exact hk a

def mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  ⟨a.val.map f, by simpa only [List.length_map] using a.property⟩

theorem mapArray_index_result {A B : Type} {N : Usize}
    (f : A → B) (a : Array A N) (i : Usize) :
    mapResult f (Array.index_usize a i) = Array.index_usize (mapArray f a) i := by
  unfold mapResult mapArray Array.index_usize
  simp only [Array.getElem?_Usize_eq, List.getElem?_map]
  cases h : a.val[i.val]? <;> rfl

/-- Map simulation for the exact finite `rangeFoldRun` interpreter. The
callback is related on every state/index pair, so fail and div results are
preserved alongside successful state mapping. -/
theorem rangeFoldRun_map {S T : Type} (f : S → T)
    (stepS : S → Usize → Result S) (stepT : T → Usize → Result T)
    (hstep : ∀ s i, mapResult f (stepS s i) = stepT (f s) i)
    (fuel : Nat) (range : AspisR1S3S9RangeFoldP6.R) (s : S) :
    mapResult f (AspisR1S3S9RangeFoldP6.rangeFoldRun fuel range stepS s) =
      AspisR1S3S9RangeFoldP6.rangeFoldRun fuel range stepT (f s) := by
  induction fuel generalizing range s with
  | zero => rfl
  | succ fuel ih =>
      unfold AspisR1S3S9RangeFoldP6.rangeFoldRun
      cases hn : AspisR1S3S9RangeFoldP6.rangeNext range with
      | fail e => simp [hn, mapResult]
      | div => simp [hn, mapResult]
      | ok pair =>
          rcases pair with ⟨item, range'⟩
          cases item with
          | none => simp [hn, mapResult]
          | some i =>
              change mapResult f (do
                let s' ← stepS s i
                AspisR1S3S9RangeFoldP6.rangeFoldRun fuel range' stepS s') =
                (do
                  let t' ← stepT (f s) i
                  AspisR1S3S9RangeFoldP6.rangeFoldRun fuel range' stepT t')
              cases hs : stepS s i with
              | fail e =>
                  have ht := hstep s i
                  simp [hs, mapResult] at ht
                  rw [← ht]
                  simp [hs, mapResult]
              | div =>
                  have ht := hstep s i
                  simp [hs, mapResult] at ht
                  rw [← ht]
                  simp [hs, mapResult]
              | ok s' =>
                  have ht := hstep s i
                  simp [hs, mapResult] at ht
                  rw [← ht]
                  simp [hs, ih]

#print axioms mapResult_bind
#print axioms mapResult_bind_congr
#print axioms mapArray_index_result
#print axioms rangeFoldRun_map

end AspisR1S9CandidateFoldMapPrimitivesV1
