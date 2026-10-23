import Query31ArrayReadback
import S9CandidateFoldMapPrimitivesV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairArrayUpdateCanonicalV1

abbrev mapResult {A B : Type} (f : A → B) (r : Result A) : Result B :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapResult f r
abbrev mapArray {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  AspisR1S9CandidateFoldMapPrimitivesV1.mapArray f a

theorem mapResult_comp {A B C : Type} (f : A → B) (g : B → C) (r : Result A) :
    mapResult g (mapResult f r) = mapResult (g ∘ f) r := by
  cases r <;> rfl

private theorem index_success_bound {A : Type} {N : Usize}
    (a : Array A N) (i : Usize) (x : A)
    (h : Array.index_usize a i = .ok x) : i.val < N.val := by
  unfold Array.index_usize at h
  cases hopt : a[i]? with
  | none => simp [hopt] at h
  | some y =>
      have hsome : a.val[i.val]? = some y := by simpa using hopt
      have hlen : i.val < a.val.length :=
        (List.getElem?_eq_some_iff.mp hsome).1
      simpa only [a.property] using hlen

/-- A nested mapped read is the same as a read after composing the element
maps. This avoids extensionality over the dependent array-length proof. -/
theorem mapArray_index_comp {A B C : Type} {n : Usize}
    (f : A → B) (g : B → C) (a : Array A n) (i : Usize) :
    Array.index_usize (mapArray g (mapArray f a)) i =
      Array.index_usize (mapArray (g ∘ f) a) i := by
  calc
    Array.index_usize (mapArray g (mapArray f a)) i =
        mapResult g (Array.index_usize (mapArray f a) i) :=
          (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result g
            (mapArray f a) i).symm
    _ = mapResult g (mapResult f (Array.index_usize a i)) :=
          congrArg (mapResult g)
            (AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result f a i).symm
    _ = mapResult (g ∘ f) (Array.index_usize a i) :=
          mapResult_comp f g (Array.index_usize a i)
    _ = Array.index_usize (mapArray (g ∘ f) a) i :=
          AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result (g ∘ f) a i

/-- One successful write preserves canonicality of every successful mapped
read. At the written index, canonicality comes from the inserted value; at
every other bounded index, the original mapped read is unchanged. -/
theorem update_preserves_canonical_reads
    {A B : Type} {n : Usize} (f : A → B) (Canonical : B → Prop)
    (a : Array A n) (i : Usize) (inserted : A) (out : Array A n)
    (hi : i.val < n.val)
    (hupdate : Array.update a i inserted = .ok out)
    (hinput : ∀ (j : Usize) (v : B),
      Array.index_usize (mapArray f a) j = .ok v → Canonical v)
    (hinserted : Canonical (f inserted)) :
    ∀ (j : Usize) (v : B),
      Array.index_usize (mapArray f out) j = .ok v → Canonical v := by
  intro j v hread
  have hj : j.val < n.val := index_success_bound (mapArray f out) j v hread
  by_cases hji : j = i
  · subst j
    have hwritten := AspisR1PublicPreparation.Query31SourceSchedule.update_readback
      a i inserted hi out hupdate
    have hmap := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result f out i
    rw [hwritten] at hmap
    have hvalue : f inserted = v := by
      apply Result.ok.inj
      calc
        .ok (f inserted) = Array.index_usize (mapArray f out) i := by
          simpa only [mapResult, AspisR1S9CandidateFoldMapPrimitivesV1.mapResult] using hmap
        _ = .ok v := hread
    simpa [hvalue] using hinserted
  · have hneq : i ≠ j := Ne.symm hji
    have hsame := AspisR1PublicPreparation.Query31SourceSchedule.update_readback_other
      a i j inserted hneq hi hj out hupdate
    have hmapOut := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result f out j
    have hmapIn := AspisR1S9CandidateFoldMapPrimitivesV1.mapArray_index_result f a j
    have hsameMapped : Array.index_usize (mapArray f out) j =
        Array.index_usize (mapArray f a) j := by
      calc
        Array.index_usize (mapArray f out) j = mapResult f (Array.index_usize out j) := hmapOut.symm
        _ = mapResult f (Array.index_usize a j) := congrArg (mapResult f) hsame
        _ = Array.index_usize (mapArray f a) j := hmapIn
    exact hinput j v (hsameMapped.symm.trans hread)

/-- The same result for a nested carrier map, matching the Pair→candidate→P6
array representation used by the S9 caller proofs. -/
theorem update_preserves_nested_canonical_reads
    {A B C : Type} {n : Usize} (f : A → B) (g : B → C)
    (Canonical : C → Prop) (a : Array A n) (i : Usize)
    (inserted : A) (out : Array A n) (hi : i.val < n.val)
    (hupdate : Array.update a i inserted = .ok out)
    (hinput : ∀ (j : Usize) (v : C),
      Array.index_usize (mapArray g (mapArray f a)) j = .ok v → Canonical v)
    (hinserted : Canonical (g (f inserted))) :
    ∀ (j : Usize) (v : C),
      Array.index_usize (mapArray g (mapArray f out)) j = .ok v → Canonical v := by
  have hinput' : ∀ (j : Usize) (v : C),
      Array.index_usize (mapArray (g ∘ f) a) j = .ok v → Canonical v := by
    intro j v hread
    apply hinput j v
    rw [mapArray_index_comp f g a j]
    exact hread
  have hresult := update_preserves_canonical_reads (g ∘ f) Canonical
    a i inserted out hi hupdate hinput' hinserted
  intro j v hread
  apply hresult j v
  rw [← mapArray_index_comp f g out j]
  exact hread

#print axioms update_preserves_canonical_reads
#print axioms update_preserves_nested_canonical_reads

end AspisR1S9PairArrayUpdateCanonicalV1
