import R1SpendDataMap
import RPv_ValueFamilyFieldTransport
import R0P.Digest

/-! Reuse the existing public/opening maps to transport the entire ordered
digest family through a field homomorphism. This is independent of concrete
field representations and keeps modular target preprocessing in Nat. -/
set_option autoImplicit false
namespace AspisR1.DigestFamilyFieldTransport
open AspisR1.ValueFamilyFieldTransport
variable {K L : Type} [Field K] [Field L]

 theorem map_keys (g : K →+* L) (pub : R0P.Public K) :
    R0P.digestKeys (SpendDataMap.mapPublic g pub) = R0P.digestKeys pub := by
  cases hr : pub.recipient <;>
    simp only [R0P.digestKeys, SpendDataMap.mapPublic, hr, Option.map]

 theorem map_row (g : K →+* L) (pub : R0P.Public K) (key : R0P.DigestKey) :
    R0P.digestRow (SpendDataMap.mapPublic g pub) key = R0P.digestRow pub key := by
  cases key <;> rfl

 theorem map_start (g : K →+* L) (pub : R0P.Public K) (key : R0P.DigestKey) :
    R0P.digestStart (SpendDataMap.mapPublic g pub) key = R0P.digestStart pub key := by
  cases key <;> rfl

 theorem map_empty_root_target (g : K →+* L) (level : Fin 20) (j : Fin 8) :
    g (R0P.emptyRootRightTarget level j : K) =
      (R0P.emptyRootRightTarget level j : L) := by
  unfold R0P.emptyRootRightTarget
  split_ifs <;> simp only [map_natCast]

 theorem map_target (g : K →+* L) (pub : R0P.Public K) (key : R0P.DigestKey) :
    (fun j => g (R0P.digestTarget pub key j)) =
      R0P.digestTarget (SpendDataMap.mapPublic g pub) key := by
  funext j
  cases key with
  | anchor => rfl
  | nullifier => rfl
  | change => rfl
  | nextRoot => rfl
  | recipient =>
    cases hr : pub.recipient <;>
      simp only [R0P.digestTarget, SpendDataMap.mapPublic, hr,
        Option.map, Option.getD, SpendDataMap.digest, map_zero]
  | frontier level =>
    by_cases hb : R0P.digestBitZero pub level
    · simpa only [R0P.digestTarget, R0P.digestBitZero, SpendDataMap.mapPublic,
        if_pos hb] using map_empty_root_target g level j
    · simp only [R0P.digestTarget, R0P.digestBitZero, SpendDataMap.mapPublic,
        if_neg hb, SpendDataMap.digest]
  | carry =>
    by_cases hc : R0P.digestCarry pub.nextPairIndex < 20
    · simp only [R0P.digestTarget, SpendDataMap.mapPublic, dif_pos hc, SpendDataMap.digest]
    · simp only [R0P.digestTarget, SpendDataMap.mapPublic, dif_neg hc, map_zero]

 theorem map_binding (g : K →+* L) (acc : R0P.Digest K) (q : K)
    (opened : Fin 16 → K) (start : Fin 9) (target : R0P.Digest K) :
    (fun j => g (R0P.digestAddBinding acc q opened start target j)) =
      R0P.digestAddBinding (fun j => g (acc j)) (g q) (fun j => g (opened j)) start
        (fun j => g (target j)) := by
  funext j
  simp only [R0P.digestAddBinding, map_add, map_mul, map_sub]

 theorem map_fold (g : K →+* L) (pub : R0P.Public K) (o : R0P.Openings K)
    (sel : R0P.Sel K) (keys : List R0P.DigestKey) (initial : R0P.Digest K) :
    (fun j => g ((keys.foldl (fun acc key =>
      R0P.digestAddBinding acc (sel (R0P.digestRow pub key)) o.z
        (R0P.digestStart pub key) (R0P.digestTarget pub key)) initial) j)) =
      keys.foldl (fun acc key => R0P.digestAddBinding acc
        (g (sel (R0P.digestRow (SpendDataMap.mapPublic g pub) key))) (mapOpenings g o).z
        (R0P.digestStart (SpendDataMap.mapPublic g pub) key)
        (R0P.digestTarget (SpendDataMap.mapPublic g pub) key)) (fun j => g (initial j)) := by
  induction keys generalizing initial with
  | nil => rfl
  | cons key keys ih =>
    simp only [List.foldl_cons]
    rw [ih, map_binding, map_target, map_row, map_start]
    rfl

 theorem map_public_digest (g : K →+* L) (pub : R0P.Public K) (o : R0P.Openings K)
    (sel : R0P.Sel K) :
    (fun j => g (R0P.publicDigestLanes pub o sel j)) =
      R0P.publicDigestLanes (SpendDataMap.mapPublic g pub) (mapOpenings g o)
        (fun i => g (sel i)) := by
  unfold R0P.publicDigestLanes
  rw [map_keys, map_fold]
  simp only [map_zero]

 theorem map_family (g : K →+* L) (pub : R0P.Public K) (o : R0P.Openings K)
    (sel : R0P.Sel K) :
    ((R0P.digestFamily (K := K)).residuals pub o sel).map g =
      (R0P.digestFamily (K := L)).residuals (SpendDataMap.mapPublic g pub)
        (mapOpenings g o) (fun i => g (sel i)) := by
  simp only [R0P.digestFamily, List.map_ofFn]
  rw [← map_public_digest]
  rfl

#print axioms map_empty_root_target
#print axioms map_target
#print axioms map_binding
#print axioms map_fold
#print axioms map_public_digest
#print axioms map_family
end AspisR1.DigestFamilyFieldTransport
