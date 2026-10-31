import NEG_RowIsolated.Types
namespace NEG_PushActual
open Aeneas Aeneas.Std
abbrev aspis_core.field.M31 := U32
abbrev aspis_core.field.CM31 := NEG_RowIsolated.aspis_core.field.CM31
abbrev aspis_core.field.QM31 := NEG_RowIsolated.aspis_core.field.QM31
structure BatchedWeights where
  «raw» : alloc.vec.Vec (Array U64 4#usize)
  terms : Usize
end NEG_PushActual
