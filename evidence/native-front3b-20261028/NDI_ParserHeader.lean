import NDF_ParserWord
import NCO_ParserShape
set_option autoImplicit false
namespace NDI_ParserHeader
open Aeneas Aeneas.Std Result

def reference (record : Slice U8) : Result Usize := do
  let a ← Slice.index_usize record 1#usize
  let b ← Slice.index_usize record 2#usize
  let bs ← (UScalar.cast .Usize b) <<< 8#i32
  let c ← Slice.index_usize record 3#usize
  let cs ← (UScalar.cast .Usize c) <<< 16#i32
  let d ← Slice.index_usize record 4#usize
  let ds ← (UScalar.cast .Usize d) <<< 24#i32
  ok ((UScalar.cast .Usize a) ||| bs ||| cs ||| ds)

def cohort (record : Slice U8) : Result Usize := do
  let a ← Slice.index_usize record 1#usize
  let b ← Slice.index_usize record 2#usize
  let c ← Slice.index_usize record 3#usize
  let d ← Slice.index_usize record 4#usize
  ok (UScalar.cast .Usize (core.num.U32.from_le_bytes (Array.make 4#usize [a,b,c,d])))

theorem reference_eq (record : Slice U8) (fit : 5 ≤ record.val.length) :
    reference record = cohort record := by
  obtain ⟨a,ha,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec record 1#usize (by scalar_tac))
  obtain ⟨b,hb,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec record 2#usize (by scalar_tac))
  obtain ⟨c,hc,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec record 3#usize (by scalar_tac))
  obtain ⟨d,hd,_⟩ := WP.spec_imp_exists (Slice.index_usize_spec record 4#usize (by scalar_tac))
  simp only [reference,cohort,ha,hb,hc,hd,bind_tc_ok]
  exact NDF_ParserWord.little_endian a b c d

#print axioms reference_eq
end NDI_ParserHeader
