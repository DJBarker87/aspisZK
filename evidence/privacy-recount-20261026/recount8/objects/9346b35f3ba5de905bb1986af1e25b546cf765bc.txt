import R1Z.ProverRwFullExternalFuns
import R1Z.ProverRwDictionaryBytesSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_Op51Source.Raw
open Aeneas Aeneas.Std Result ControlFlow Error ProverRwFull
abbrev aspis_core.field.wide_exact.WideExact.to_limbs := ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.to_limbs
/-- [prover_rw_success_p6::wide_bytes_flat]:
    Source: 'lib.rs', lines 127:0-131:1
    Visibility: public -/
def wide_bytes_flat
  (x : aspis_core.field.wide_exact.WideExact) :
  Result (Array Std.U8 32#usize)
  := do
  let l ← aspis_core.field.wide_exact.WideExact.to_limbs x
  let i ← Array.index_usize l 0#usize
  let a ← lift (core.num.U32.to_le_bytes i)
  let i1 ← Array.index_usize l 1#usize
  let b ← lift (core.num.U32.to_le_bytes i1)
  let i2 ← Array.index_usize l 2#usize
  let c ← lift (core.num.U32.to_le_bytes i2)
  let i3 ← Array.index_usize l 3#usize
  let d ← lift (core.num.U32.to_le_bytes i3)
  let i4 ← Array.index_usize l 4#usize
  let e ← lift (core.num.U32.to_le_bytes i4)
  let i5 ← Array.index_usize l 5#usize
  let f ← lift (core.num.U32.to_le_bytes i5)
  let i6 ← Array.index_usize l 6#usize
  let g ← lift (core.num.U32.to_le_bytes i6)
  let i7 ← Array.index_usize l 7#usize
  let h ← lift (core.num.U32.to_le_bytes i7)
  let i8 ← Array.index_usize a 0#usize
  let i9 ← Array.index_usize a 1#usize
  let i10 ← Array.index_usize a 2#usize
  let i11 ← Array.index_usize a 3#usize
  let i12 ← Array.index_usize b 0#usize
  let i13 ← Array.index_usize b 1#usize
  let i14 ← Array.index_usize b 2#usize
  let i15 ← Array.index_usize b 3#usize
  let i16 ← Array.index_usize c 0#usize
  let i17 ← Array.index_usize c 1#usize
  let i18 ← Array.index_usize c 2#usize
  let i19 ← Array.index_usize c 3#usize
  let i20 ← Array.index_usize d 0#usize
  let i21 ← Array.index_usize d 1#usize
  let i22 ← Array.index_usize d 2#usize
  let i23 ← Array.index_usize d 3#usize
  let i24 ← Array.index_usize e 0#usize
  let i25 ← Array.index_usize e 1#usize
  let i26 ← Array.index_usize e 2#usize
  let i27 ← Array.index_usize e 3#usize
  let i28 ← Array.index_usize f 0#usize
  let i29 ← Array.index_usize f 1#usize
  let i30 ← Array.index_usize f 2#usize
  let i31 ← Array.index_usize f 3#usize
  let i32 ← Array.index_usize g 0#usize
  let i33 ← Array.index_usize g 1#usize
  let i34 ← Array.index_usize g 2#usize
  let i35 ← Array.index_usize g 3#usize
  let i36 ← Array.index_usize h 0#usize
  let i37 ← Array.index_usize h 1#usize
  let i38 ← Array.index_usize h 2#usize
  let i39 ← Array.index_usize h 3#usize
  ok
    (Array.make 32#usize [
      i8, i9, i10, i11, i12, i13, i14, i15, i16, i17, i18, i19, i20, i21, i22,
      i23, i24, i25, i26, i27, i28, i29, i30, i31, i32, i33, i34, i35, i36,
      i37, i38, i39
      ])

end R1Z.PV_CB3_Op51Source.Raw

namespace R1Z.PV_CB3_Op51Source
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
/-- Select the complete extracted owned reference, whose arbitrary-input
source equivalence is checked by kani-wide-flat-001 (no stubs). -/
def selected (ops : ExternalFuns) : ExternalFuns :=
  {ops with op51 := Raw.wide_bytes_flat}
theorem op51_source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op51 x = Raw.wide_bytes_flat x := rfl
#print axioms op51_source
end R1Z.PV_CB3_Op51Source
