import R1SemanticPublicWire

/-! Injectivity of the semantic carrier-to-model projection.  This is a
field-preservation fact about the Lean representation; it does not identify
the carrier with a Rust parser or wire encoding. -/
set_option autoImplicit false
namespace AspisR1.SemanticPublicWireInjective

open AspisR1.SemanticPublicWire

private theorem transfer_common_eq {c c' : Common} {r r' : Digest}
    (h : toPublic (.transfer c r) = toPublic (.transfer c' r')) : c = c' := by
  cases c with
  | mk anchor nullifier assetId change nextPairIndex snapshotFrontier nextRoot nextFrontier =>
    cases c' with
    | mk anchor' nullifier' assetId' change' nextPairIndex' snapshotFrontier' nextRoot' nextFrontier' =>
      have hAnchor : anchor = anchor' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.anchor) h
      have hNullifier : nullifier = nullifier' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.nullifier) h
      have hAsset : assetId = assetId' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.assetId) h
      have hChange : change = change' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.change) h
      have hIndexVal : nextPairIndex.val = nextPairIndex'.val := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.nextPairIndex) h
      have hIndex : nextPairIndex = nextPairIndex' := Fin.ext hIndexVal
      have hSnapshot : snapshotFrontier = snapshotFrontier' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.snapshotFrontier) h
      have hRoot : nextRoot = nextRoot' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.nextRoot) h
      have hFrontier : nextFrontier = nextFrontier' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.nextFrontier) h
      subst anchor'
      subst nullifier'
      subst assetId'
      subst change'
      subst nextPairIndex'
      subst snapshotFrontier'
      subst nextRoot'
      subst nextFrontier'
      rfl

private theorem withdrawal_common_eq {c c' : Common} {a a' : M31}
    (h : toPublic (.withdrawal c a) = toPublic (.withdrawal c' a')) : c = c' := by
  cases c with
  | mk anchor nullifier assetId change nextPairIndex snapshotFrontier nextRoot nextFrontier =>
    cases c' with
    | mk anchor' nullifier' assetId' change' nextPairIndex' snapshotFrontier' nextRoot' nextFrontier' =>
      have hAnchor : anchor = anchor' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.anchor) h
      have hNullifier : nullifier = nullifier' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.nullifier) h
      have hAsset : assetId = assetId' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.assetId) h
      have hChange : change = change' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.change) h
      have hIndexVal : nextPairIndex.val = nextPairIndex'.val := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.nextPairIndex) h
      have hIndex : nextPairIndex = nextPairIndex' := Fin.ext hIndexVal
      have hSnapshot : snapshotFrontier = snapshotFrontier' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.snapshotFrontier) h
      have hRoot : nextRoot = nextRoot' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.nextRoot) h
      have hFrontier : nextFrontier = nextFrontier' := by
        simpa [toPublic] using congrArg (fun p : R0P.Public M31 => p.nextFrontier) h
      subst anchor'
      subst nullifier'
      subst assetId'
      subst change'
      subst nextPairIndex'
      subst snapshotFrontier'
      subst nextRoot'
      subst nextFrontier'
      rfl

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
