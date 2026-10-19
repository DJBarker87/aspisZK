import R0Z.FsAbortBounds
import Mathlib.Data.FinEnum

/-! R1 games (zf1/DESIGN-R1-GAMES §2): lawful lenses as coordinate splits.
`HitFresh` / `PairFresh` (FsAbortBounds) ask for an equivalence `S ≃ R × U`
in which the designated field of an address is the `U` coordinate.  A lawful
lens `S → U` gives one (`R` = the lens fibre over a fixed point), so the
freshness facts reduce to three checkable properties: the lens leaves the
event and the other address unchanged, and the designated field of the
address is the lens value.  Also: 32-byte answers, their byte encoding and
the fixed-offset / trailing field readers (the `fixed 0` and `trailing`
readers of the spend-path RawByteCollisionTargets, restated here). -/
set_option autoImplicit false
noncomputable section
namespace R1Z.LensR1
open R0Z.FsAbortBounds
attribute [local instance] Classical.propDecidable

abbrev Bytes := List UInt8
abbrev Ans := Fin 32 → UInt8

/-! ### Lawful lenses -/

structure Lens (S U : Type) where
  get : S → U
  set : S → U → S
  get_set : ∀ s u, get (set s u) = u
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s u u', set (set s u) u' = set s u'

/-- The fibre of a lens over `u₀` times the lens value. -/
def Lens.equiv {S U : Type} (L : Lens S U) (u₀ : U) : S ≃ {s : S // L.get s = u₀} × U where
  toFun s := (⟨L.set s u₀, L.get_set s u₀⟩, L.get s)
  invFun p := L.set p.1.1 p.2
  left_inv s := by
    show L.set (L.set s u₀) (L.get s) = s
    rw [L.set_set, L.set_get]
  right_inv p := by
    obtain ⟨⟨r, hr⟩, u⟩ := p
    have h1 : L.set (L.set r u) u₀ = r := by
      rw [L.set_set, ← hr, L.set_get]
    have h2 : L.get (L.set r u) = u := L.get_set r u
    exact Prod.ext (Subtype.ext h1) h2

theorem Lens.equiv_symm {S U : Type} (L : Lens S U) (u₀ : U) (r : {s : S // L.get s = u₀})
    (u : U) : (L.equiv u₀).symm (r, u) = L.set r.1 u := rfl

/-- Hit freshness from a lens: the event and (on the event) the adversary read
are unchanged by the lens, and the designated field of the address is the
lens value. -/
theorem hitFresh_of_lens {S U A : Type} [Fintype S] [Fintype U] [Nonempty U]
    (L : Lens S U) (D : S → Prop) (qa ga : S → A) (fld : A → U) (Umin : ℕ)
    (hcard : Umin ≤ Fintype.card U)
    (hD : ∀ s u, D s → D (L.set s u))
    (hq : ∀ s u, D s → qa (L.set s u) = qa s)
    (hf : ∀ s u, fld (ga (L.set s u)) = u) :
    HitFresh D qa ga Umin := by
  let u₀ : U := Classical.arbitrary U
  refine ⟨{s : S // L.get s = u₀}, U, inferInstance, inferInstance, inferInstance,
    L.equiv u₀, fun _ a => fld a, hcard, ?_, ?_, ?_⟩
  · intro r u u' h
    rw [Lens.equiv_symm] at h ⊢
    have := hD _ u' h
    rwa [L.set_set] at this
  · intro r u u' h
    rw [Lens.equiv_symm] at h ⊢
    rw [Lens.equiv_symm, ← L.set_set r.1 u u', hq _ u' h]
  · intro r u a h
    rw [Lens.equiv_symm] at h
    rw [← h]
    exact (hf r.1 u).symm

/-- Pair freshness from a lens: the first address is unchanged by the lens and
the designated field of the second is the lens value. -/
theorem pairFresh_of_lens {S U A : Type} [Fintype S] [Fintype U] [Nonempty U]
    (L : Lens S U) (fa ga : S → A) (fld : A → U) (Umin : ℕ)
    (hcard : Umin ≤ Fintype.card U)
    (hfa : ∀ s u, fa (L.set s u) = fa s)
    (hf : ∀ s u, fld (ga (L.set s u)) = u) :
    PairFresh fa ga Umin := by
  let u₀ : U := Classical.arbitrary U
  refine Or.inr ⟨{s : S // L.get s = u₀}, U, inferInstance, inferInstance, inferInstance,
    L.equiv u₀, fun _ a => fld a, hcard, ?_, ?_⟩
  · intro r u u'
    rw [Lens.equiv_symm, Lens.equiv_symm, hfa, hfa]
  · intro r u a h
    rw [Lens.equiv_symm] at h
    rw [← h]
    exact (hf r.1 u).symm

theorem pairFresh_of_ne {S A : Type} [Fintype S] (fa ga : S → A) (Umin : ℕ)
    (h : ∀ s, fa s ≠ ga s) : PairFresh fa ga Umin := Or.inl h

/-! ### Lens constructions -/

/-- A lens on one coordinate of a family of attempts, with an untouched factor. -/
def Lens.pi {N : ℕ} {C T U : Type} (k : Fin N) (L : Lens C U) :
    Lens ((Fin N → C) × T) U where
  get ct := L.get (ct.1 k)
  set ct u := (Function.update ct.1 k (L.set (ct.1 k) u), ct.2)
  get_set ct u := by
    show L.get (Function.update ct.1 k (L.set (ct.1 k) u) k) = u
    simp [L.get_set]
  set_get ct := by
    obtain ⟨c, t⟩ := ct
    show (Function.update c k (L.set (c k) (L.get (c k))), t) = (c, t)
    rw [L.set_get, Function.update_eq_self]
  set_set ct u u' := by
    obtain ⟨c, t⟩ := ct
    show (Function.update (Function.update c k (L.set (c k) u)) k
        (L.set (Function.update c k (L.set (c k) u) k) u'), t) =
      (Function.update c k (L.set (c k) u'), t)
    simp [L.set_set]

theorem Lens.pi_set_fst_ne {N : ℕ} {C T U : Type} (k : Fin N) (L : Lens C U)
    (ct : (Fin N → C) × T) (u : U) (j : Fin N) (hj : j ≠ k) :
    ((Lens.pi (T := T) k L).set ct u).1 j = ct.1 j := by
  simp [Lens.pi, Function.update_of_ne hj]

theorem Lens.pi_set_fst_eq {N : ℕ} {C T U : Type} (k : Fin N) (L : Lens C U)
    (ct : (Fin N → C) × T) (u : U) :
    ((Lens.pi (T := T) k L).set ct u).1 k = L.set (ct.1 k) u := by
  simp [Lens.pi]

theorem Lens.pi_set_snd {N : ℕ} {C T U : Type} (k : Fin N) (L : Lens C U)
    (ct : (Fin N → C) × T) (u : U) :
    ((Lens.pi (T := T) k L).set ct u).2 = ct.2 := rfl

/-! ### 32-byte answers -/

def ans (u : Ans) : Bytes := List.ofFn u

theorem length_ans (u : Ans) : (ans u).length = 32 := List.length_ofFn

/-- The 32-byte field at offset 0 (spend-path `fixed 0`). -/
def fixed0 (a : Bytes) : Ans := fun i => a.getD i.val 0

/-- The trailing 32-byte field (spend-path `trailing`). -/
def trailing (a : Bytes) : Ans := fun i => a.getD (a.length - 32 + i.val) 0

theorem getD_ans (u : Ans) (i : Fin 32) : ((ans u)[i.val]?).getD 0 = u i := by
  have h : i.val < (List.ofFn u).length := by rw [List.length_ofFn]; exact i.isLt
  rw [ans, List.getElem?_eq_getElem h, Option.getD_some, List.getElem_ofFn]

theorem fixed0_ans_append (u : Ans) (t : Bytes) : fixed0 (ans u ++ t) = u := by
  funext i
  have hi : i.val < (ans u).length := by rw [length_ans]; exact i.isLt
  simp only [fixed0, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  exact getD_ans u i

theorem trailing_append_ans (p : Bytes) (u : Ans) : trailing (p ++ ans u) = u := by
  funext i
  have hl : (p ++ ans u).length - 32 + i.val = p.length + i.val := by
    simp only [List.length_append, length_ans]
    omega
  simp only [trailing, hl, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact getD_ans u i

/-! ### The answer space has 2^256 points -/

def uint8Equiv : UInt8 ≃ Fin UInt8.size where
  toFun := UInt8.toFin
  invFun := UInt8.ofFin
  left_inv x := UInt8.ofFin_toFin x
  right_inv x := UInt8.toFin_ofFin x

theorem card_ans : Fintype.card Ans = 2 ^ 256 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_congr uint8Equiv, Fintype.card_fin]
  norm_num [UInt8.size]

theorem umin_le_card_ans : 2 ^ 255 ≤ Fintype.card Ans := by
  rw [card_ans]
  exact Nat.pow_le_pow_right (by norm_num) (by norm_num)

#print axioms Lens.equiv
#print axioms hitFresh_of_lens
#print axioms pairFresh_of_lens
#print axioms pairFresh_of_ne
#print axioms Lens.pi
#print axioms Lens.pi_set_fst_ne
#print axioms Lens.pi_set_fst_eq
#print axioms fixed0_ans_append
#print axioms trailing_append_ans
#print axioms card_ans
#print axioms umin_le_card_ans
end R1Z.LensR1
