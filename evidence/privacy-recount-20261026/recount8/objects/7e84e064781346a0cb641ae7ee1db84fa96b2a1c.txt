import R1Z.BuilderRecordsReference

/-! Reuse the existing raw-owned extraction. Shipped raw association is the
all-words no-stub Kani06 P6 gate, not a Lean source theorem. -/
set_option autoImplicit false
namespace R1Z.PV_RunJoin_RawExtraction
open Aeneas Aeneas.Std Result

abbrev raw := AspisBuilderRecordsReference.pool_v1.pair_forest_copy_builder.records_reference.raw_owned

theorem all_words (d : Array U32 8#usize) : raw d = ok d := BuilderRecordsReference.raw_owned d

theorem lane (d : Array U32 8#usize) (i : Fin 8) :
    (do let out ← raw d; ok out.val[i.val]!) = ok d.val[i.val]! := by
  rw [all_words]
  rfl

#print axioms raw
#print axioms all_words
#print axioms lane
end R1Z.PV_RunJoin_RawExtraction
