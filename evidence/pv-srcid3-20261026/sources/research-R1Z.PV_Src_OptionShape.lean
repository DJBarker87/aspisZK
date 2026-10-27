import R1Z.BuilderCanonical

/-! Public-option shape is preserved and reflected by the characteristic-p
embedding. Consequently the canonical relation already supplies the shape
required by the extracted public input encoding. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_OptionShape
open R1J.SpendWitnessMap
variable {K : Type} [Field K] [DecidableEq K] [CharP K 2147483647]

theorem reflect (p : R0P.Public F)
    (h : AspisR1.PublicOptionShape.canonical (mapPub (K := K) p)) :
    AspisR1.PublicOptionShape.canonical p := by
  cases hv : p.variant with
  | privateTransfer =>
    obtain ⟨r,hr,ha⟩ := AspisR1.PublicOptionShape.private_transfer_shape
      (mapPub (K := K) p) hv h
    unfold AspisR1.PublicOptionShape.canonical
    rw [hv]
    change p.recipient.isSome = true ∧ p.withdrawalAmount = none
    constructor
    · cases he : p.recipient with
      | none => simp [mapPub,he] at hr
      | some d => rfl
    · cases he : p.withdrawalAmount with
      | none => rfl
      | some a => simp [mapPub,he] at ha
  | withdrawal =>
    obtain ⟨a,hne,ha,hr⟩ := AspisR1.PublicOptionShape.withdrawal_shape
      (mapPub (K := K) p) hv h
    unfold AspisR1.PublicOptionShape.canonical
    rw [hv]
    change p.recipient.isNone = true ∧ p.withdrawalAmount.isSome = true ∧
      p.withdrawalAmount ≠ some 0
    constructor
    · cases he : p.recipient with
      | none => rfl
      | some d => simp [mapPub,he] at hr
    constructor
    · cases he : p.withdrawalAmount with
      | none => simp [mapPub,he] at ha
      | some b => rfl
    · intro hz
      have hz' : (mapPub (K := K) p).withdrawalAmount = some 0 := by
        simp only [mapPub,hz,Option.map_some,map_zero]
      exact hne (Option.some.inj (ha.symm.trans hz'))

theorem canonical [Fintype K]
    [Algebra (ZMod AspisCircleGroupOrder.P) K]
    (i : BuilderCanonical.Instance (K := K)) :
    AspisR1.PublicOptionShape.canonical i.val.1 :=
  reflect _ i.property.1.1

#print axioms reflect
#print axioms canonical
end R1Z.PV_Src_OptionShape
