import R1Z.BuilderRecordsReference
import R1Z.BuilderRecordsFields

/-! The extracted owned mapper is total even outside the caller's admitted
value domain. These are source-reference facts, not a P6 shipped-equality
certificate and not a counterexample to a valid release fixture. -/
set_option autoImplicit false
namespace R1Z.PV_Src_RecordRangeObstruction
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderRecordsReference
open AspisBuilderRecordsReference.pool_v1.pair_forest_copy_builder

/-- Any successful actual reference return retains the out-value, so a bound
on that input is necessary for the words field. -/
theorem output_bound_required
    (input : Input) (out : U32) (rec : Option Note) (chg : Note)
    (snapshot : Snapshot) (asset : U32) (empty : Roots) (w : RW) (p : RP)
    (hr : records_reference.records_reference_with_roots
      input out rec chg snapshot asset empty = ok (w,p))
    (hw : WitnessOk (BuilderExtractedRecords.rawWitness w)) : out.val < 2^30 := by
  have hf := BuilderRecordsFields.fixed_fields input out rec chg snapshot asset empty w p hr
  have hb := hw.values.2.1
  change w.output_value.val < 2^30 at hb
  rw [hf.1] at hb
  exact hb

/-- No range condition is checked by this callee. The boundary value is a
legal U32. The actual extracted computation succeeds but WitnessOk fails. -/
theorem reference_counterexample
    (input : Input) (rec : Option Note) (chg : Note)
    (snapshot : Snapshot) (asset : U32) (empty : Roots) :
    ∃ w p, records_reference.records_reference_with_roots
      input 1073741824#u32 rec chg snapshot asset empty = ok (w,p) ∧
      ¬ WitnessOk (BuilderExtractedRecords.rawWitness w) := by
  refine ⟨witness input 1073741824#u32 rec chg,
    publicRecord rec snapshot asset empty,
    BuilderRecordsReference.records input 1073741824#u32 rec chg snapshot asset empty, ?_⟩
  intro hw
  have hb := hw.values.2.1
  change (2^30 : Nat) < 2^30 at hb
  exact (Nat.lt_irrefl _) hb

#print axioms output_bound_required
#print axioms reference_counterexample
end R1Z.PV_Src_RecordRangeObstruction
