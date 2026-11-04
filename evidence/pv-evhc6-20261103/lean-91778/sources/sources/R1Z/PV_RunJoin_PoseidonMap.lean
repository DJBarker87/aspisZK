import R0P.Semantics

/-! Field-homomorphism naturality for the scalar Poseidon model. These lemmas
are purely algebraic: no field characteristic, constant correspondence, or
finite-field computation is assumed. -/

set_option autoImplicit false

namespace R1Z.PV_RunJoin_PoseidonMap

open R0P

variable {K L : Type} [Field K] [Field L] (f : K →+* L)

attribute [local irreducible] poseidonPermutation

abbrev State (K : Type) := Fin 16 → K
abbrev Digest (K : Type) := Fin 8 → K

def mapState (s : State K) : State L := fun i => f (s i)
def mapDigest (d : Digest K) : Digest L := fun i => f (d i)

theorem map_poseidonPow5 (x : K) :
    f (poseidonPow5 x) = poseidonPow5 (f x) := by
  simp [poseidonPow5]

theorem map_poseidonMat4 (s : Fin 4 → K) (i : Fin 4) :
    f (poseidonMat4 s i) = poseidonMat4 (fun i => f (s i)) i := by
  fin_cases i <;> simp [poseidonMat4, map_add]

theorem map_poseidonExternalLinear (s : State K) :
    mapState (K := K) (L := L) f (poseidonExternalLinear s) =
      poseidonExternalLinear (mapState (K := K) (L := L) f s) := by
  funext i
  dsimp only [poseidonExternalLinear, mapState]
  simp_rw [map_add, map_zero, map_poseidonMat4]

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
  dsimp only [poseidonInternalLinear, mapState]
  have hxs : (List.ofFn (fun j : Fin 15 => s j.succ)).map f =
      List.ofFn (fun j : Fin 15 => f (s j.succ)) := by
    simp
  by_cases hi : i.val = 0
  · simp only [dif_pos hi, map_sub]
    rw [map_foldl_add, hxs, map_zero]
  · simp only [dif_neg hi, map_add, map_mul, map_natCast]
    rw [map_foldl_add, hxs, map_zero]

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
  unfold poseidonInternalRound
  rw [map_poseidonInternalLinear]
  have hinput :
      mapState (K := K) (L := L) f (fun i =>
        if i = 0 then poseidonPow5 (s 0 + c) else s i) =
      (fun i => if i = 0 then poseidonPow5
        (mapState (K := K) (L := L) f s 0 + f c)
        else mapState (K := K) (L := L) f s i) := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [mapState, map_add, map_poseidonPow5]
    · simp [mapState, hi]
  rw [hinput]

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

theorem map_fullRoundFold (cs : List (State K)) (s : State K) :
    mapState (K := K) (L := L) f (cs.foldl poseidonFullRound s) =
      (cs.map (mapState (K := K) (L := L) f)).foldl poseidonFullRound
        (mapState (K := K) (L := L) f s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
      calc
        mapState (K := K) (L := L) f ((c :: cs).foldl poseidonFullRound s) =
            mapState (K := K) (L := L) f (cs.foldl poseidonFullRound
              (poseidonFullRound s c)) := rfl
        _ = (cs.map (mapState (K := K) (L := L) f)).foldl poseidonFullRound
              (mapState (K := K) (L := L) f (poseidonFullRound s c)) := ih _
        _ = (cs.map (mapState (K := K) (L := L) f)).foldl poseidonFullRound
              (poseidonFullRound (mapState (K := K) (L := L) f s)
                (mapState (K := K) (L := L) f c)) := by rw [map_poseidonFullRound]
        _ = ((c :: cs).map (mapState (K := K) (L := L) f)).foldl poseidonFullRound
              (mapState (K := K) (L := L) f s) := rfl

theorem map_internalRoundFold (cs : List K) (s : State K) :
    mapState (K := K) (L := L) f (cs.foldl poseidonInternalRound s) =
      (cs.map f).foldl poseidonInternalRound (mapState (K := K) (L := L) f s) := by
  induction cs generalizing s with
  | nil => rfl
  | cons c cs ih =>
      calc
        mapState (K := K) (L := L) f ((c :: cs).foldl poseidonInternalRound s) =
            mapState (K := K) (L := L) f (cs.foldl poseidonInternalRound
              (poseidonInternalRound s c)) := rfl
        _ = (cs.map f).foldl poseidonInternalRound
              (mapState (K := K) (L := L) f (poseidonInternalRound s c)) := ih _
        _ = (cs.map f).foldl poseidonInternalRound
              (poseidonInternalRound (mapState (K := K) (L := L) f s) (f c)) := by
                rw [map_poseidonInternalRound]
        _ = ((c :: cs).map f).foldl poseidonInternalRound
              (mapState (K := K) (L := L) f s) := rfl

theorem map_poseidonPermutation (s : State K) :
    mapState (K := K) (L := L) f (poseidonPermutation s) =
      poseidonPermutation (mapState (K := K) (L := L) f s) := by
  unfold poseidonPermutation
  change mapState (K := K) (L := L) f
      ((List.ofFn (fun r : Fin 4 => poseidonExternalFinal (K := K) r)).foldl
        poseidonFullRound
        ((List.ofFn (fun r : Fin 14 => poseidonInternalConstants (K := K) r)).foldl
          poseidonInternalRound
          ((List.ofFn (fun r : Fin 4 => poseidonExternalInitial (K := K) r)).foldl
            poseidonFullRound (poseidonExternalLinear s)))) =
    (List.ofFn (fun r : Fin 4 => poseidonExternalFinal (K := L) r)).foldl
      poseidonFullRound
      ((List.ofFn (fun r : Fin 14 => poseidonInternalConstants (K := L) r)).foldl
        poseidonInternalRound
        ((List.ofFn (fun r : Fin 4 => poseidonExternalInitial (K := L) r)).foldl
          poseidonFullRound (poseidonExternalLinear (mapState (K := K) (L := L) f s))))
  have hi : (List.ofFn (fun r : Fin 4 => poseidonExternalInitial (K := K) r)).map
      (mapState (K := K) (L := L) f) =
      List.ofFn (fun r : Fin 4 => poseidonExternalInitial (K := L) r) := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (by
      funext r
      exact funext (map_poseidonExternalInitial f r))
  have hc : (List.ofFn (fun r : Fin 14 => poseidonInternalConstants (K := K) r)).map f =
      List.ofFn (fun r : Fin 14 => poseidonInternalConstants (K := L) r) := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (by
      funext r
      exact map_poseidonInternalConstants f r)
  have hf : (List.ofFn (fun r : Fin 4 => poseidonExternalFinal (K := K) r)).map
      (mapState (K := K) (L := L) f) =
      List.ofFn (fun r : Fin 4 => poseidonExternalFinal (K := L) r) := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (by
      funext r
      exact funext (map_poseidonExternalFinal f r))
  rw [map_fullRoundFold, hf]
  rw [map_internalRoundFold, hc]
  rw [map_fullRoundFold, hi]
  rw [map_poseidonExternalLinear]

theorem map_nodeCompress (a b : Digest K) :
    mapDigest (K := K) (L := L) f (nodeCompress a b) =
      nodeCompress (mapDigest (K := K) (L := L) f a)
        (mapDigest (K := K) (L := L) f b) := by
  change (fun i : Fin 8 => f (poseidonPermutation (fun l =>
      if h : l.val < 8 then a ⟨l.val, h⟩
      else if l.val = 15 then b 7 - (1051521018 : K)
      else b ⟨l.val - 8, by omega⟩) ⟨i.val, by omega⟩)) = _
  have hinput : mapState (K := K) (L := L) f (fun l =>
      if h : l.val < 8 then a ⟨l.val, h⟩
      else if l.val = 15 then b 7 - (1051521018 : K)
      else b ⟨l.val - 8, by omega⟩) =
    (fun l => if h : l.val < 8 then f (a ⟨l.val, h⟩)
      else if l.val = 15 then f (b 7) - (1051521018 : L)
      else f (b ⟨l.val - 8, by omega⟩)) := by
    funext l
    dsimp only [mapState]
    split_ifs with hlow hlast
    · rfl
    · rw [map_sub]
      exact congrArg (fun z : L => f (b 7) - z) (map_natCast f 1051521018)
    · rfl
  funext i
  let inK : State K := fun l =>
    if h : l.val < 8 then a ⟨l.val, h⟩
    else if l.val = 15 then b 7 - (1051521018 : K)
    else b ⟨l.val - 8, by omega⟩
  let inL : State L := fun l =>
    if h : l.val < 8 then f (a ⟨l.val, h⟩)
    else if l.val = 15 then f (b 7) - (1051521018 : L)
    else f (b ⟨l.val - 8, by omega⟩)
  change mapState (K := K) (L := L) f (poseidonPermutation inK)
      ⟨i.val, by omega⟩ = poseidonPermutation inL ⟨i.val, by omega⟩
  rw [congrFun (map_poseidonPermutation f inK) ⟨i.val, by omega⟩]
  rw [hinput]

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

#print axioms map_poseidonPow5
#print axioms map_poseidonMat4
#print axioms map_poseidonExternalLinear
#print axioms map_foldl_add
#print axioms map_poseidonInternalLinear
#print axioms map_poseidonFullRound
#print axioms map_poseidonInternalRound
#print axioms map_poseidonExternalInitial
#print axioms map_poseidonExternalFinal
#print axioms map_poseidonInternalConstants
#print axioms map_fullRoundFold
#print axioms map_internalRoundFold
#print axioms map_poseidonPermutation
#print axioms map_nodeCompress

end R1Z.PV_RunJoin_PoseidonMap
