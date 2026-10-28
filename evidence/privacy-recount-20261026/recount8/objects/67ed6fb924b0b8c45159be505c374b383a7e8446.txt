import R1Z.ProverRwDictionaryDomain
import R1Z.ProverRwDictionaryBytesSource
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryBytes
open Aeneas Aeneas.Std Result ProverRwFull
namespace Src
abbrev limbs := ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.to_limbs
abbrev parse := ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_le_bytes
abbrev write := ProverRwDictionaryBytesSource.aspis_core.field.QM31.write_le_bytes
abbrev complex := ProverRwDictionaryBytesSource.aspis_core.field.CM31.new
end Src
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryDomain.selected ops with
    op49 := Src.limbs,op50 := Src.parse,op60 := Src.complex,op72 := Src.write}

theorem limbs_source (ops : ExternalFuns) (x : aspis_core.field.wide_exact.WideExact) :
    (selected ops).op49 x = .ok (Array.make 8#usize
      [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
       x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]) := rfl

theorem parse_source (ops : ExternalFuns) (bytes : Slice U8) :
    (selected ops).op50 bytes = Src.parse bytes := rfl

theorem write_source (ops : ExternalFuns) (x : aspis_core.field.QM31) (out : Slice U8) :
    (selected ops).op72 x out = Src.write x out := rfl

theorem complex_source (ops : ExternalFuns) (a b : U32) :
    (selected ops).op60 a b = .ok ⟨a,b⟩ := rfl

/-- Wrong-length inputs are rejected before any byte indexing or decoding. -/
theorem reject_length (ops : ExternalFuns) (bytes : Slice U8)
    (h : Slice.len bytes ≠ 32#usize) : (selected ops).op50 bytes = .ok none := by
  rw [parse_source]
  unfold Src.parse ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.from_le_bytes
    ProverRwDictionaryBytesSource.aspis_core.field.wide_exact.WideExact.BYTE_LEN
  have hn : (Slice.len bytes != 32#usize) = true := by
    simpa only [bne_iff_ne] using h
  dsimp only
  rw [hn]
  rfl

#print axioms limbs_source
#print axioms parse_source
#print axioms write_source
#print axioms complex_source
#print axioms reject_length
end R1Z.ProverRwDictionaryBytes
