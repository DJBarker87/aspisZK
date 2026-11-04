import Aeneas
/-! Explicit external library representation for the salt cone.
`Zeroizing` is represented by its live payload. Allocation/drop behaviour
is outside the per-leaf address theorem; no allocator law is asserted. -/
namespace AspisR1ProverCommit
inductive alloc.collections.TryReserveError where
  | capacity
abbrev zeroize.Zeroizing (Z : Type) := Z
end AspisR1ProverCommit
