import Aeneas
import AspisR1PublicPreparation.Types

namespace KSA_Isolated
open Aeneas Aeneas.Std Result
/- Reused representation from
 aeneas-verif/v7-k13-onefold-batch-source-20260827/generated/V7K13AddBatch/TypesExternal.lean:19-24. -/
structure core.slice.iter.Windows (T : Type) where
  slice : Slice T
  width : Std.Usize
  index : Nat
/- Reuse the cohort producer's two-QM31 record, not an opaque type.
 docs/research/100bit-spend-path-20261013/lean/bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/Types.lean:321-323.
 Conversion to the release QM31 carrier is an explicit obligation. -/
abbrev aspis_core.field.wide_exact.WideExact :=
  AspisR1PublicPreparation.aspis_core.field.WideExact
/- Same transparent newtype representation as
 docs/research/100bit-spend-path-20261013/evidence/session-b-fibre-point-extraction-20261019/sources/Types.lean:32.
 The checked constructor, not this representation, enforces the bound. -/
abbrev aspis_core.r0.domain.FibreIndex := Std.Usize

end KSA_Isolated
