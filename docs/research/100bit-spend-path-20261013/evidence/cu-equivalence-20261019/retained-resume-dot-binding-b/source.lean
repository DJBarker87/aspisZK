import CuSavingsRetainedResumeOrigins
import CuSavingsRetainedDotsResumed
import AspisR1RhoTransactions.FunsExternal
set_option autoImplicit false
namespace AspisR1.CuSavingsRetainedResumeDotBinding
open Aeneas Aeneas.Std Result
abbrev Q := AspisR1RhoQuery.aspis_core.field.WideExact
abbrev I := CuSavingsRetainedSamplerBinding.I
abbrev P := CuSavingsRetainedSamplerBinding.E
def input (e : Q) : I :=
  ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
def fromInput (e : I) : Q :=
  ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
def table {N : Usize} (xs : Array I N) : Array Q N :=
  ⟨xs.val.map fromInput,by simp only [List.length_map,xs.property]⟩
def toPrepared (e : Q) : P := CuSavingsRetainedSamplerBinding.fromInput (input e)
def preparedTable {N : Usize} (xs : Array Q N) : Array P N :=
  ⟨xs.val.map toPrepared,by simp only [List.length_map,xs.property]⟩
def powers (N : Usize) (e : Q) : Result (Array Q N) := do
  let values←AspisR1CanonicalInputs.weights.powers N (input e)
  .ok (table values)
@[reducible] def binding (common : AspisR1RhoTransactions.TxCommon) : AspisR1RhoTransactions.TxCommon :=
  {common with powers:=powers}

variable [AspisR1CanonicalDots.Shared] [AspisR1CanonicalSampler.Shared]
  [AspisR1CanonicalReader.Runtime] [AspisR1CanonicalKReader.Runtime] [AspisR1CuRho.ScalarKBlocks]

theorem input_origin (e : Q) (h : CuSavingsRetainedResumeOrigins.ReaderOrigin e) :
    CuSavingsCanonicalDotsSources.SourceValue (input e) := by
  obtain ⟨reader,after,value,hr,he⟩:=h
  subst e
  exact .resumed reader after value hr

theorem powers_success (common : AspisR1RhoTransactions.TxCommon) (N : Usize)
    (base : Q) (out : Array Q N)
    (h : letI : AspisR1RhoTransactions.TxCommon:=binding common
         AspisR1RhoTransactions.weights.powers N base=.ok out) :
    ∃ source,AspisR1CanonicalInputs.weights.powers N (input base)=.ok source ∧ out=table source := by
  change powers N base=.ok out at h
  unfold powers at h
  cases hs : AspisR1CanonicalInputs.weights.powers N (input base) with
  | fail error => simp only [hs,bind_tc_fail] at h;cases h
  | div => simp only [hs,bind_tc_div] at h;cases h
  | ok values => simp only [hs,bind_tc_ok] at h;exact ⟨values,rfl,(Result.ok.inj h).symm⟩

theorem prepared_table {N : Usize} (values : Array I N) :
    preparedTable (table values)=CuSavingsRetainedSamplerBinding.table values := by
  cases values with | mk values bound =>
    simp only [preparedTable,table,List.map_map,CuSavingsRetainedSamplerBinding.table]
    rfl

theorem query_equivalence {O : Type} (common : AspisR1RhoTransactions.TxCommon)
    (dotCommon : AspisR1RetainedDots.Shared) (base : Q)
    (hb : CuSavingsRetainedResumeOrigins.ReaderOrigin base) (out : Array Q 29#usize)
    (hp : letI : AspisR1RhoTransactions.TxCommon:=binding common
          AspisR1RhoTransactions.weights.powers 29#usize base=.ok out)
    (view : AspisR1CuQuery.verifier.View) (index : Usize)
    (ctx : Slice U8→(Unit→Result (Array CuSavingsRetainedDotsBinding.E 4#usize))→Result O) :
    (do let bytes←AspisR1CuQuery.verifier.View.query view index
        ctx bytes (fun _=>@AspisR1RetainedDots.prefix_new_dots.four_dots
          (CuSavingsRetainedDotsBinding.newShared dotCommon) bytes
          (CuSavingsRetainedDotsInputs.gamma (preparedTable out)))) =
      (do let bytes←AspisR1CuQuery.verifier.View.query view index
          ctx bytes (fun _=>@AspisR1RetainedDots.old_dots.four_dots
            (CuSavingsRetainedDotsBinding.oldShared dotCommon) bytes
            (CuSavingsRetainedDotsInputs.gamma (preparedTable out)))) := by
  obtain ⟨values,hs,ho⟩:=powers_success common 29#usize base out hp
  subst out
  rw [prepared_table]
  exact CuSavingsRetainedDotsResumed.source_powers_query dotCommon (input base)
    (input_origin base hb) values hs view index ctx

#print axioms input_origin
#print axioms powers_success
#print axioms prepared_table
#print axioms query_equivalence
end AspisR1.CuSavingsRetainedResumeDotBinding
