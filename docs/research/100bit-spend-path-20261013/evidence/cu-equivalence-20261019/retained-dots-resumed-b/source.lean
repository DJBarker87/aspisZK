import CuSavingsRetainedDotsInputs
import CuSavingsRetainedDotsRepresentation
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedDotsResumed
open Aeneas Aeneas.Std Result AspisR1RetainedDots
open CuSavingsRetainedDotsBinding CuSavingsRetainedDotsTail CuSavingsRetainedDotsInputs
variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]

theorem source_powers_query {O : Type} (common : Shared)
    (base : CuSavingsRetainedSamplerBinding.I)
    (hb : CuSavingsCanonicalDotsSources.SourceValue base)
    (values : Array CuSavingsRetainedSamplerBinding.I 29#usize)
    (hp : AspisR1CanonicalInputs.weights.powers 29#usize base=.ok values)
    (view : AspisR1CuQuery.verifier.View) (index : Usize)
    (ctx : Slice U8→(Unit→Result (Array E 4#usize))→Result O) :
    (do let bytes←AspisR1CuQuery.verifier.View.query view index
        ctx bytes (fun _=>@prefix_new_dots.four_dots (newShared common) bytes
          (gamma (CuSavingsRetainedSamplerBinding.table values)))) =
      (do let bytes←AspisR1CuQuery.verifier.View.query view index
          ctx bytes (fun _=>@old_dots.four_dots (oldShared common) bytes
            (gamma (CuSavingsRetainedSamplerBinding.table values)))) := by
  apply query_equivalence common view index _ ?_ ctx
  intro i hi
  have hb' : CuSavingsCanonicalDotsSources.SourceValue
      (CuSavingsRetainedSamplerBinding.input (CuSavingsRetainedSamplerBinding.fromInput base)) := by
    simpa only [CuSavingsRetainedSamplerInputs.input_fromInput] using hb
  have hp' : AspisR1CanonicalInputs.weights.powers 29#usize
      (CuSavingsRetainedSamplerBinding.input (CuSavingsRetainedSamplerBinding.fromInput base))=.ok values := by
    simpa only [CuSavingsRetainedSamplerInputs.input_fromInput] using hp
  exact CuSavingsRetainedSamplerInputs.table_sources 29#usize
    (CuSavingsRetainedSamplerBinding.fromInput base) hb' values hp' i hi

theorem reader_powers_query {O : Type} (common : Shared)
    (reader after : AspisR1CanonicalReader.Reader)
    (base : AspisR1CanonicalReader.field.wide_exact.WideExact)
    (hr : AspisR1CanonicalReader.Reader.e reader=.ok (.Ok base,after))
    (values : Array CuSavingsRetainedSamplerBinding.I 29#usize)
    (hp : AspisR1CanonicalInputs.weights.powers 29#usize
      (AspisR1CanonicalReader.toInput base)=.ok values)
    (view : AspisR1CuQuery.verifier.View) (index : Usize)
    (ctx : Slice U8→(Unit→Result (Array E 4#usize))→Result O) :
    (do let bytes←AspisR1CuQuery.verifier.View.query view index
        ctx bytes (fun _=>@prefix_new_dots.four_dots (newShared common) bytes
          (gamma (CuSavingsRetainedSamplerBinding.table values)))) =
      (do let bytes←AspisR1CuQuery.verifier.View.query view index
          ctx bytes (fun _=>@old_dots.four_dots (oldShared common) bytes
            (gamma (CuSavingsRetainedSamplerBinding.table values)))) :=
  source_powers_query common _ (.resumed reader after base hr) values hp view index ctx

#print axioms source_powers_query
#print axioms reader_powers_query
end AspisR1.CuSavingsRetainedDotsResumed
