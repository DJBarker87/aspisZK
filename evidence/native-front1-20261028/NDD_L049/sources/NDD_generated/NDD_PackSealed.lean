import NDD_PackPrefix
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NDD_PackSealed
open FIq_Native NDD_PackModel

/-- A checked concrete prefix, sealed only to prevent kernel normalization of
array-copy back-functions during continuation transport. No law is assumed. -/
structure Prefix where
  run : {α : Type} → Slice field.QM31 →
    (field.QM31 → field.QM31 → field.QM31 → field.QM31 → Result α) → Result α
  bind : ∀ {α β : Type} (values : Slice field.QM31)
    (k : field.QM31 → field.QM31 → field.QM31 → field.QM31 → Result α) (g : α → Result β),
    (do let a ← run values k;g a) = run values (fun a b c d => do let x ← k a b c d;g x)
  source : ∀ values, field.qm31_pack_base4 values = run values tail

opaque concrete : Prefix :=
  { run := NDD_PackPrefix.prefixWith
    bind := NDD_PackPrefix.bind_prefix
    source := NDD_PackPrefix.source_prefix }

theorem concrete_source (values : Slice field.QM31) :
    field.qm31_pack_base4 values = concrete.run values tail := concrete.source values
#print axioms concrete_source
end NDD_PackSealed
