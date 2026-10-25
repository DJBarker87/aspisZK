import Hist_EncoderTrace
import S2W_FirstOccurrence
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_ReaderProjection
open Aeneas Aeneas.Std Result S2W_Trace S2W_OuterOccurrences Hist_EncoderTrace

theorem marked (event : Event) (pub : Slice U8)
    (selected : readerPublic event = some pub) : mark event = some true := by
  cases event with
  | returned call value => cases call <;> simp_all [readerPublic,mark]

theorem empty_of_no_reader (log : Log) (absent : true ∉ tags log) : readerPublics log = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro pub member
  obtain ⟨event,inLog,selected⟩ := List.mem_filterMap.mp member
  exact absent (List.mem_filterMap.mpr ⟨event,inLog,marked event pub selected⟩)

theorem first_empty (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts : Slice AdapterRw.Cuts.Account) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (log : Log)
    (execution : run ops (S2W_Outer.stage1_owned ops S2W_Outer.traceEffects program accounts data)
      [] = ok (.Ok saved,log)) : readerPublics log = [] := by
  apply empty_of_no_reader
  rw [S2W_FirstOccurrence.first_occurrence ops program accounts data saved log execution]
  simp

#print axioms marked
#print axioms empty_of_no_reader
#print axioms first_empty
end AspisR1.Hist_ReaderProjection
end
