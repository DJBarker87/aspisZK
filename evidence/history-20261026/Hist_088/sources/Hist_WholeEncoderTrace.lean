import Hist_ReaderProjection
import S2W_Observation
import S2W_TraceSplice
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hist_WholeEncoderTrace
open Aeneas Aeneas.Std Result S2W_Trace S2W_OuterErasure S2W_TraceFacts
open Hist_EncoderTrace Hist_ReaderProjection

theorem second_public (ops : AdapterRw.Ops) (program : AdapterRw.solana_pubkey.Pubkey)
    (accounts1 accounts2 : Slice AdapterRw.Cuts.Account) (data1 data2 : Slice U8)
    (slot : core.result.Result U64 AdapterRw.Cuts.PE) (saved : alloc.vec.Vec U8)
    (accepted1 : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program accounts1 data1 = ok (.Ok saved))
    (accepted2 : AdapterRw.r1_pool_adapter.owned.stage2_owned ops program accounts2 data2 slot = ok (.Ok ()))
    (validated : AdapterRw.r1_pool_adapter.ValidatedAsqa) (encoded : Array U8 1880#usize)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops program accounts2 data2 slot = ok (.Ok validated))
    (encoder : ops.op22 validated.statement = ok (.Ok encoded))
    (log : Log)
    (execution : run ops (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot)
      [] = ok (.Ok saved,log)) : readerPublics log = [encoded.to_slice] := by
  obtain ⟨l1,h1⟩ := success_exists ops _ [] (.Ok saved)
    ((stage1_erasure ops program accounts1 data1).trans accepted1)
  obtain ⟨l2,h2⟩ := success_exists ops _ [] (.Ok ())
    ((stage2_erasure ops program accounts2 data2 slot).trans accepted2)
  have shifted := S2W_TraceSplice.run_shift ops
    (S2W_Outer.stage2_owned ops S2W_Outer.traceEffects program accounts2 data2 slot) l1 []
  simp only [List.append_nil,h2,thenResult] at shifted
  have whole : run ops (S2W_Observation.two ops program accounts1 data1 accounts2 data2 slot) [] =
      ok (.Ok saved,l1 ++ l2) := by
    simp only [S2W_Observation.two,run_bind,h1,shifted,thenResult]
    rfl
  have same := congrArg Prod.snd (Result.ok.inj (execution.symm.trans whole))
  rw [same]
  simp only [readerPublics,List.filterMap_append]
  rw [show l1.filterMap readerPublic = [] from first_empty ops program accounts1 data1 saved l1 h1]
  exact Hist_EncoderTrace.second_public ops program accounts2 data2 slot validated encoded validation encoder l2 h2

#print axioms second_public
end AspisR1.Hist_WholeEncoderTrace
end
