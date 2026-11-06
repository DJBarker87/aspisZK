# Printed scanner roots

Exact successful elaboration at L062; standard axioms. Hypothesis inventory: NKL_CUTS.md / NKL_ROW_PACKETS.json.

```text
theorem NKL_ScanRoot.deployed : ∀ (proof : Std.Array U8 57607#usize) (out : Reply) (events : List Check)
  (after : Bytes),
  Invoke (checks proof.to_slice) out events (↑proof) after →
    ok out =
        NJS_Extract.verifier.candidate.canonical_scan AspisR1M31Parser.field.M31.from_le_bytes
          NKL_CanonicalInstallation.childK NKL_CanonicalInstallation.childE NKL_CanonicalInstallation.childCV
          proof.to_slice ∧
      after = ↑proof ∧ ∃ suffix, events ++ suffix = checks proof.to_slice :=
⋯
theorem NKL_ScanRoot.adopted : ∀ (proof : Std.Array U8 57607#usize) (out : Reply) (events : List Check) (after : Bytes),
  Invoke (checks proof.to_slice) out events (↑proof) after →
    ok out = do
      let valid ← MultiproofParserRef.parser_reference.scan proof.to_slice
      ok (NKB_CanonicalOpening.reply valid) :=
⋯
theorem NKL_ScanRoot.no_later_event : ∀ (proof : Std.Array U8 57607#usize) (events : List Check) (after : Bytes),
  Invoke (checks proof.to_slice) (core.result.Result.Err NJS_Extract.verifier.Error.Parse) events (↑proof) after →
    ∃ before bad suffix,
      checks proof.to_slice = before ++ bad :: suffix ∧
        events = before ++ [bad] ∧ before.all nativeGuard = true ∧ nativeGuard bad = false :=
⋯
'NKL_ScanRoot.all_source' depends on axioms: [propext, Classical.choice, Quot.sound]
'NKL_ScanRoot.deployed' depends on axioms: [propext, Classical.choice, Quot.sound]
'NKL_ScanRoot.adopted' depends on axioms: [propext, Classical.choice, Quot.sound]
'NKL_ScanRoot.no_later_event' depends on axioms: [propext, Classical.choice, Quot.sound]
'NKL_ScanRoot.success_events' depends on axioms: [propext, Classical.choice, Quot.sound]

```
