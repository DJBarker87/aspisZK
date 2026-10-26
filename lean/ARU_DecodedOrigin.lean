import SCH_SourceCuts
import P2P_Origin
import DrvC_NativeDecode
import DrvC_SourceEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARU_DecodedOrigin
open Aeneas Aeneas.Std Result MultiproofConeCanonical S2W_NativeConsolidation
open S2W_ExtractionBoundary

/-- The accepted source decoder supplies the very semantic public passed to
TX1. All cuts and decoder facts are OUTPUTS of the two source calls. -/
theorem pair (ops : AdapterRw.Ops) (id : Program) (accounts1 accounts2 : Accounts)
    (data1 data2 : Slice U8) (slot : Slot) (saved : alloc.vec.Vec U8)
    (first : AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts1 data1 = ok (.Ok saved))
    (second : AdapterRw.r1_pool_adapter.owned.stage2_owned ops id accounts2 data2 slot = ok (.Ok ())) :
    ∃ f s, SourceCuts ops accounts1 accounts2 saved f s ∧
      Port1_Driver.decodeSemantic ops f.pub = ok (some f.semantic) ∧
      P2P_Origin.Fact ops id accounts2 data2 slot s := by
  obtain ⟨pa,pu,pub,raw,statement,semantic,proof,split,ip,iu,rp,ru,dec,valid,sem,range1,called,len⟩ :=
    DrvC_NativeDecode.first_call_decoded ops id accounts1 data1 saved first
  have shape1 := AdapterRw.Ranges.suffix_exact raw proof 688#usize 58295#usize (by scalar_tac) (by simpa using len) range1
  have start : (688#usize : Usize).val = 688 := by scalar_tac
  have finish1 : (58295#usize : Usize).val = 58295 := by scalar_tac
  rw [start,finish1] at shape1
  have proofLength : (bytesOf proof.val).length = 57607 := by
    simp only [bytesOf,List.length_map]
    omega
  have suffix1 : bytesOf raw.val = (bytesOf raw.val).take 688 ++ bytesOf proof.val := by
    simpa only [bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape1.2
  obtain ⟨validated,pa2,ca2,raw2,cp2,encoded,proof2,finish,validation,ip2,ic2,rp2,rc2,encoding,range2,called2,len2⟩ :=
    S2X.second_fixed_range ops id accounts2 data2 slot second
  have shape2 := (AdapterRw.Ranges.suffix_exact raw2 proof2 688#usize finish
    (S2X.successful_range_ordered raw2 proof2 688#usize finish range2) len2 range2).2
  change raw2.val = raw2.val.take 688 ++ proof2.val at shape2
  have suffix2 : bytesOf raw2.val = (bytesOf raw2.val).take 688 ++ bytesOf proof2.val := by
    simpa only [bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape2
  refine ⟨⟨pa,pu,raw,pub,statement,semantic,proof,split⟩,
    ⟨pa2,ca2,raw2,cp2,encoded,proof2,finish⟩,
    ⟨ip,iu,rp,ru,dec,called,proofLength,suffix1,ip2,ic2,rp2,rc2,range2,len2,called2,suffix2⟩,?_⟩
  exact ⟨by simp only [Port1_Driver.decodeSemantic,dec,valid,sem,bind_tc_ok],⟨validated,validation,encoding⟩⟩

#print axioms pair
end AspisR1.ARU_DecodedOrigin
end
