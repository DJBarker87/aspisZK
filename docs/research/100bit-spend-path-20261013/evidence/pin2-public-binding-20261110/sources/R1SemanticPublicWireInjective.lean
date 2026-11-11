import R1SemanticPublicWire

/-! Injectivity of the semantic carrier-to-model projection.  This is a
field-preservation fact about the Lean representation; it does not identify
the carrier with a Rust parser or wire encoding. -/
set_option autoImplicit false
namespace AspisR1.SemanticPublicWireInjective

open AspisR1.SemanticPublicWire

/-- Two carriers that agree on every projected field are equal (PIN2 fields
included; `Bytes32` and the destination are recovered from their byte lists). -/
private theorem common_eq_of_public {c c' : Common} {p p' : R0P.Public M31}
    (hp : p = p')
    (h1 : p.anchor = c.anchor) (h1' : p'.anchor = c'.anchor)
    (h2 : p.nullifier = c.nullifier) (h2' : p'.nullifier = c'.nullifier)
    (h3 : p.assetId = c.assetId) (h3' : p'.assetId = c'.assetId)
    (h4 : p.change = c.change) (h4' : p'.change = c'.change)
    (h5 : p.nextPairIndex = c.nextPairIndex.val) (h5' : p'.nextPairIndex = c'.nextPairIndex.val)
    (h6 : p.snapshotFrontier = c.snapshotFrontier)
    (h6' : p'.snapshotFrontier = c'.snapshotFrontier)
    (h7 : p.nextRoot = c.nextRoot) (h7' : p'.nextRoot = c'.nextRoot)
    (h8 : p.nextFrontier = c.nextFrontier) (h8' : p'.nextFrontier = c'.nextFrontier)
    (h9 : p.pool = c.pool.val) (h9' : p'.pool = c'.pool.val)
    (h10 : p.deploymentDomain = c.deploymentDomain.val)
    (h10' : p'.deploymentDomain = c'.deploymentDomain.val)
    (h11 : p.destination = c.destination.map Subtype.val)
    (h11' : p'.destination = c'.destination.map Subtype.val) : c = c' := by
  rw [← hp] at h1' h2' h3' h4' h5' h6' h7' h8' h9' h10' h11'
  have e1 : c.anchor = c'.anchor := h1.symm.trans h1'
  have e2 : c.nullifier = c'.nullifier := h2.symm.trans h2'
  have e3 : c.assetId = c'.assetId := h3.symm.trans h3'
  have e4 : c.change = c'.change := h4.symm.trans h4'
  have e5 : c.nextPairIndex = c'.nextPairIndex := Fin.ext (h5.symm.trans h5')
  have e6 : c.snapshotFrontier = c'.snapshotFrontier := h6.symm.trans h6'
  have e7 : c.nextRoot = c'.nextRoot := h7.symm.trans h7'
  have e8 : c.nextFrontier = c'.nextFrontier := h8.symm.trans h8'
  have e9 : c.pool = c'.pool := Subtype.ext (h9.symm.trans h9')
  have e10 : c.deploymentDomain = c'.deploymentDomain := Subtype.ext (h10.symm.trans h10')
  have e11 : c.destination = c'.destination :=
    Option.map_injective Subtype.val_injective (h11.symm.trans h11')
  cases c
  cases c'
  dsimp only at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  subst e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11
  rfl

private theorem transfer_common_eq {c c' : Common} {r r' : Digest}
    (h : toPublic (.transfer c r) = toPublic (.transfer c' r')) : c = c' :=
  common_eq_of_public h rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

private theorem withdrawal_common_eq {c c' : Common} {a a' : M31}
    (h : toPublic (.withdrawal c a) = toPublic (.withdrawal c' a')) : c = c' :=
  common_eq_of_public h rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl rfl rfl

theorem toPublic_injective : Function.Injective toPublic := by
  intro w w' h
  cases w with
  | transfer c recipient =>
    cases w' with
    | transfer c' recipient' =>
      have hc : c = c' := transfer_common_eq h
      have hr : recipient = recipient' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.recipient) h
      subst c'
      subst recipient'
      rfl
    | withdrawal c' amount' =>
      have hv := congrArg (fun p : R0P.Public M31 => p.variant) h
      simp [toPublic] at hv
  | withdrawal c amount =>
    cases w' with
    | transfer c' recipient' =>
      have hv := congrArg (fun p : R0P.Public M31 => p.variant) h
      simp [toPublic] at hv
    | withdrawal c' amount' =>
      have hc : c = c' := withdrawal_common_eq h
      have ha : amount = amount' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.withdrawalAmount) h
      subst c'
      subst amount'
      rfl

#print axioms toPublic_injective
end AspisR1.SemanticPublicWireInjective
