import S1ValuesOwnedInstallationV1
set_option autoImplicit false
namespace PCWC_S1_Obligation
open Aeneas Aeneas.Std Result

/-- PCWC-OBLIGATION (for P3, NOT proved here, not attempted).
The gate installs `AspisS1ValuesOwnedInstallation.expandValues` (the owned-buffer reference
`AspisS1ValuesOwned.values_owned_reference` wrapped by `toVec`/`toSlice`) as the caller operation `op11`
(`withValues`, `nativeValues`).  The frozen function it stands for is
`compact::expand_values` at crates/aspis-r1-cost-probe/src/compact.rs:127 (revision 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387).
`FrozenExpandValues` is a parameter for the future P1 extraction of that function (no gate constant exists for it:
the gate takes op11 abstractly); its type is exactly the type of `op11`.

Equality obligation: on every pair of slices whose doubled length does not overflow `Usize`, the frozen extraction
and the reference return the same `Result` value: same status (`Ok ()` or `Err Length`) and same output slice
(unchanged on `Err`, the 32-byte-cell expansion on `Ok`).  The hypothesis `2*input.length ≤ Usize.max` is the one
carried by `AspisS1ValuesOwnedExact.installed_exact`; every Rust slice satisfies it (len ≤ isize::MAX), the Lean
`Slice` carrier does not force it, and the two sides differ on overflow (reference: `2#usize * len` fails; frozen
release build: wrapping unless overflow checks are on, then panic).  The statement therefore carries the premise
explicitly, and the Slice-carrier-to-Rust-slice correspondence stays a separate (runtime/SDK) matter.
`CodecError` is the frozen extraction's own type (`AspisR1CurrentCaller.compact.CodecError`), not a copy: the gate's
`AspisS1ValuesOwned.CodecError` is an abbrev to it, so the status component needs no transport. The reconstructed
crate (PCWC_S1_RECONSTRUCTION.json) has a local three-variant enum with the same variant names; the replacement of
that local enum by the frozen type in the gate Funs is mechanical post-processing step T3, itself an assumption. -/
def ExpandValuesFrozenEq
    (FrozenExpandValues : Slice U8 → Slice U8 →
      Result ((core.result.Result Unit AspisR1CurrentCaller.compact.CodecError) × Slice U8)) : Prop :=
  ∀ (input output : Slice U8), 2*input.length ≤ Usize.max →
    FrozenExpandValues input output = AspisS1ValuesOwnedInstallation.expandValues input output

/- Not stated as a theorem on purpose; the form P3 must prove once the frozen emission exists:
theorem expand_values_matches_frozen : ExpandValuesFrozenEq <the P1 emission of compact::expand_values> := by
  sorry  -- OBLIGATION, not attempted in PCWC_ -/

#print axioms ExpandValuesFrozenEq
end PCWC_S1_Obligation
