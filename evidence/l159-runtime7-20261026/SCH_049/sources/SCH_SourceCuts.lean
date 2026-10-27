import S2W_NativeConsolidation
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCH_SourceCuts
open Aeneas Aeneas.Std Result MultiproofConeCanonical S2W_NativeConsolidation
open S2W_ExtractionBoundary

/-- Cut existence from SOURCE acceptance, independently of native extraction
or syscall totality. The actual two calls supply every witness. -/
theorem pair (ops : AdapterRw.Ops) (id : Program) (accounts1 accounts2 : Accounts)
    (data1 data2 : Slice U8) (slot : Slot) (saved : alloc.vec.Vec U8)
    (first : AdapterRw.r1_pool_adapter.owned.stage1_owned ops id accounts1 data1 = ok (.Ok saved))
    (second : AdapterRw.r1_pool_adapter.owned.stage2_owned ops id accounts2 data2 slot = ok (.Ok ())) :
    ∃ f s, SourceCuts ops accounts1 accounts2 saved f s := by
  obtain ⟨pa,pu,pub,raw,statement,semantic,proof,split,ip,iu,rp,ru,dec,called,len,shape⟩ :=
    AdapterRw.LeadInputs.first_byte_fields ops id accounts1 data1 saved first
  obtain ⟨validated,pa2,ca2,raw2,cp2,encoded,proof2,finish,_,ip2,ic2,rp2,rc2,_,range,called2,len2⟩ :=
    S2X.second_fixed_range ops id accounts2 data2 slot second
  have shape2 := (AdapterRw.Ranges.suffix_exact raw2 proof2 688#usize finish
    (S2X.successful_range_ordered raw2 proof2 688#usize finish range) len2 range).2
  change raw2.val = raw2.val.take 688 ++ proof2.val at shape2
  have suffix2 : bytesOf raw2.val = (bytesOf raw2.val).take 688 ++ bytesOf proof2.val := by
    simpa only [bytesOf,List.map_append,List.map_take] using congrArg bytesOf shape2
  exact ⟨⟨pa,pu,raw,pub,statement,semantic,proof,split⟩,
    ⟨pa2,ca2,raw2,cp2,encoded,proof2,finish⟩,
    ⟨ip,iu,rp,ru,dec,called,len,shape,ip2,ic2,rp2,rc2,range,len2,called2,suffix2⟩⟩

#print axioms pair
end AspisR1.SCH_SourceCuts
end
