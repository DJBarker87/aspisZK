import R0P.Semantics

/-! Field-homomorphism naturality for the scalar Poseidon model. These lemmas
are purely algebraic: no field characteristic, constant correspondence, or
finite-field computation is assumed. -/

set_option autoImplicit false

namespace AspisR1.PoseidonMap

open R0P

variable {K L : Type} [Field K] [Field L] (f : K →+* L)

abbrev State (K : Type) := Fin 16 → K
abbrev Digest (K : Type) := Fin 8 → K

def mapState (s : State K) : State L := fun i => f (s i)
def mapDigest (d : Digest K) : Digest L := fun i => f (d i)

theorem map_poseidonPow5 (x : K) :
    f (poseidonPow5 x) = poseidonPow5 (f x) := by
  simp [poseidonPow5]

theorem map_poseidonMat4 (s : Fin 4 → K) :
    (fun i => f (poseidonMat4 s i)) = poseidonMat4 (fun i => f (s i)) := by
  funext i
  fin_cases i <;> simp [poseidonMat4, map_add]

theorem map_poseidonExternalLinear (s : State K) :
    mapState (K := K) (L := L) f (poseidonExternalLinear s) =
      poseidonExternalLinear (mapState (K := K) (L := L) f s) := by
  funext i
  simp only [poseidonExternalLinear, mapState, map_add]
  congr 1
  · exact congrFun (map_poseidonMat4 f _) _
  · congr 1
    · exact congrFun (map_poseidonMat4 f _) _
    · exact congrFun (map_poseidonMat4 f _) _
    · exact congrFun (map_poseidonMat4 f _) _
    · exact congrFun (map_poseidonMat4 f _) _

theorem map_foldl_add (xs : List K) (init : K) :
    f (xs.foldl (· + ·) init) = (xs.map f).foldl (· + ·) (f init) := by
  induction xs generalizing init with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih, map_add]

theorem map_poseidonInternalLinear (s : State K) :
    mapState (K := K) (L := L) f (poseidonInternalLinear s) =
      poseidonInternalLinear (mapState (K := K) (L := L) f s) := by
  funext i
  simp only [poseidonInternalLinear, mapState]
  have hxs : (List.ofFn (fun j : Fin 15 => f (s j.succ))) =
      (List.ofFn (fun j : Fin 15 => s j.succ)).map f := by
    simp
  rw [map_foldl_add, hxs]
  by_cases hi : i.val = 0
  · simp only [if_pos hi, map_sub]
  · simp only [if_neg hi, map_add, map_mul, map_natCast]

theorem map_poseidonFullRound (s c : State K) :
    mapState (K := K) (L := L) f (poseidonFullRound s c) =
      poseidonFullRound (mapState (K := K) (L := L) f s)
        (mapState (K := K) (L := L) f c) := by
  rw [poseidonFullRound, map_poseidonExternalLinear]
  congr 1
  funext i
  simp only [mapState, map_add, map_poseidonPow5]

theorem map_poseidonInternalRound (s : State K) c :
    mapState (K := K) (L := L) f (poseidonInternalRound s c) =
      poseidonInternalRound (mapState (K := K) (L := L) f s) (f c) := by
  rw [poseidonInternalRound, map_poseidonInternalLinear]
  funext i
  by_cases hi : i = 0
  · subst i
    simp [mapState, map_add, map_poseidonPow5]
  · simp [mapState, hi]

theorem map_poseidonExternalInitial (r : Fin 4) (i : Fin 16) :
    f (poseidonExternalInitial (K := K) r i) =
      poseidonExternalInitial (K := L) r i := by
  fin_cases r <;> fin_cases i <;> simp [poseidonExternalInitial]

theorem map_poseidonExternalFinal (r : Fin 4) (i : Fin 16) :
    f (poseidonExternalFinal (K := K) r i) =
      poseidonExternalFinal (K := L) r i := by
  fin_cases r <;> fin_cases i <;> simp [poseidonExternalFinal]

theorem map_poseidonInternalConstants (r : Fin 14) :
    f (poseidonInternalConstants (K := K) r) =
      poseidonInternalConstants (K := L) r := by
  fin_cases r <;> simp [poseidonInternalConstants]

private theorem map_fullRoundFold (cs : List (State K)) (s : State K) :
    mapState (K := K) (L := L) f (cs.foldl poseidonFullRound s) =
      (cs.map (mapState (K := K) (L := L) f)).foldl poseidonFullRound
        (mapState (K := K) (L := L) f s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih, map_poseidonFullRound]

private theorem map_internalRoundFold (cs : List K) (s : State K) :
    mapState (K := K) (L := L) f (cs.foldl poseidonInternalRound s) =
      (cs.map f).foldl poseidonInternalRound (mapState (K := K) (L := L) f s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih, map_poseidonInternalRound]

theorem map_poseidonPermutation (s : State K) :
    mapState (K := K) (L := L) f (poseidonPermutation s) =
      poseidonPermutation (mapState (K := K) (L := L) f s) := by
  unfold poseidonPermutation
  simp only [map_poseidonExternalLinear]
  rw [map_fullRoundFold]
  simp only [List.map_ofFn]
  rw [map_internalRoundFold]
  simp only [List.map_ofFn]
  rw [map_fullRoundFold]
  simp only [List.map_ofFn]

theorem map_nodeCompress (a b : Digest K) :
    mapDigest (K := K) (L := L) f (nodeCompress a b) =
      nodeCompress (mapDigest (K := K) (L := L) f a)
        (mapDigest (K := K) (L := L) f b) := by
  funext i
  change f ((poseidonPermutation _ ) ⟨i.val, by omega⟩) = _
  rw [congrFun (map_poseidonPermutation f _) ⟨i.val, by omega⟩]
  congr 1
  funext lane
  by_cases h₁ : lane.val < 8
  · simp only [if_pos h₁]
  · simp only [if_neg h₁]
    by_cases h₂ : lane.val = 15
    · simp only [if_pos h₂, map_sub]
    · simp only [if_neg h₂]

#print axioms map_poseidonPow5
#print axioms map_poseidonMat4
#print axioms map_poseidonExternalLinear
#print axioms map_poseidonInternalLinear
#print axioms map_poseidonFullRound
#print axioms map_poseidonInternalRound
#print axioms map_poseidonExternalInitial
#print axioms map_poseidonExternalFinal
#print axioms map_poseidonInternalConstants
#print axioms map_poseidonPermutation
#print axioms map_nodeCompress

end AspisR1.PoseidonMap
