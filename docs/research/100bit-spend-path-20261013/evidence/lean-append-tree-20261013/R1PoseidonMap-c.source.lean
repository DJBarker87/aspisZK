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
  let localK : Fin 4 → Fin 4 → K := fun g =>
    poseidonMat4 (fun lane => s ⟨4 * g.val + lane.val, by omega⟩)
  let localL : Fin 4 → Fin 4 → L := fun g =>
    poseidonMat4 (fun lane => f (s ⟨4 * g.val + lane.val, by omega⟩))
  have hlocal (g : Fin 4) (c : Fin 4) : f (localK g c) = localL g c := by
    exact congrFun (map_poseidonMat4 f (fun lane => s ⟨4 * g.val + lane.val, by omega⟩)) c
  funext i
  simp only [poseidonExternalLinear, mapState, map_add, localK, localL]
  rw [hlocal, hlocal, hlocal, hlocal, hlocal]

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
  have hxs : (List.ofFn (fun j : Fin 15 => s j.succ)).map f =
      List.ofFn (fun j : Fin 15 => f (s j.succ)) := by
    simp
  by_cases hi : i.val = 0
  · simp only [if_pos hi, map_sub]
    rw [map_foldl_add, hxs]
  · simp only [if_neg hi, map_add, map_mul, map_natCast]
    rw [map_foldl_add, hxs]

theorem map_poseidonFullRound (s c : State K) :
    mapState (K := K) (L := L) f (poseidonFullRound s c) =
      poseidonFullRound (mapState (K := K) (L := L) f s)
        (mapState (K := K) (L := L) f c) := by
  unfold poseidonFullRound
  rw [map_poseidonExternalLinear]
  have hinput :
      mapState (K := K) (L := L) f (fun lane => poseidonPow5 (s lane + c lane)) =
        (fun lane => poseidonPow5
          (mapState (K := K) (L := L) f s lane + mapState (K := K) (L := L) f c lane)) := by
    funext i
    simp [mapState, map_add, map_poseidonPow5]
  rw [hinput]

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
  fin_cases r <;> fin_cases i <;> exact map_natCast f _

theorem map_poseidonExternalFinal (r : Fin 4) (i : Fin 16) :
    f (poseidonExternalFinal (K := K) r i) =
      poseidonExternalFinal (K := L) r i := by
  fin_cases r <;> fin_cases i <;> exact map_natCast f _

theorem map_poseidonInternalConstants (r : Fin 14) :
    f (poseidonInternalConstants (K := K) r) =
      poseidonInternalConstants (K := L) r := by
  fin_cases r <;> exact map_natCast f _

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
  rw [map_poseidonExternalLinear]
  rw [map_fullRoundFold]
  have hi : (List.ofFn (fun r : Fin 4 => poseidonExternalInitial (K := K) r)).map
      (mapState (K := K) (L := L) f) =
      List.ofFn (fun r : Fin 4 => poseidonExternalInitial (K := L) r) := by
    simp only [List.map_ofFn]
    congr 1
    funext r
    funext i
    exact map_poseidonExternalInitial f r i
  rw [hi]
  rw [map_internalRoundFold]
  have hc : (List.ofFn (fun r : Fin 14 => poseidonInternalConstants (K := K) r)).map f =
      List.ofFn (fun r : Fin 14 => poseidonInternalConstants (K := L) r) := by
    simp only [List.map_ofFn]
    congr 1
    funext r
    exact map_poseidonInternalConstants f r
  rw [hc]
  rw [map_fullRoundFold]
  have hf : (List.ofFn (fun r : Fin 4 => poseidonExternalFinal (K := K) r)).map
      (mapState (K := K) (L := L) f) =
      List.ofFn (fun r : Fin 4 => poseidonExternalFinal (K := L) r) := by
    simp only [List.map_ofFn]
    congr 1
    funext r
    funext i
    exact map_poseidonExternalFinal f r i
  rw [hf]

theorem map_nodeCompress (a b : Digest K) :
    mapDigest (K := K) (L := L) f (nodeCompress a b) =
      nodeCompress (mapDigest (K := K) (L := L) f a)
        (mapDigest (K := K) (L := L) f b) := by
  change mapDigest (K := K) (L := L) f (fun i =>
    poseidonPermutation (fun l =>
      if h : l.val < 8 then a ⟨l.val, h⟩
      else if l.val = 15 then b 7 - (1051521018 : K)
      else b ⟨l.val - 8, by omega⟩) i) = _
  have hinput : mapState (K := K) (L := L) f (fun l =>
      if h : l.val < 8 then a ⟨l.val, h⟩
      else if l.val = 15 then b 7 - (1051521018 : K)
      else b ⟨l.val - 8, by omega⟩) =
    (fun l => if h : l.val < 8 then f (a ⟨l.val, h⟩)
      else if l.val = 15 then f (b 7) - (1051521018 : L)
      else f (b ⟨l.val - 8, by omega⟩)) := by
    funext l
    by_cases h₁ : l.val < 8
    · simp [h₁]
    · simp only [h₁, if_false]
      by_cases h₂ : l.val = 15
      · simp [h₂, map_sub, map_natCast]
      · simp [h₂]
  funext i
  rw [congrFun (map_poseidonPermutation f _) ⟨i.val, by omega⟩, hinput]

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
