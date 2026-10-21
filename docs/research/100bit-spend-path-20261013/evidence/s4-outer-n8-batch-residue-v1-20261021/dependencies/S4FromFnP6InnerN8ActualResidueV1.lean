import S4FromFnP6InnerN8ActualCanonicalV1

open Aeneas Aeneas.Std Result AspisR1FastDotsCurrent
set_option autoImplicit false
namespace AspisR1FromFnP6Generated

theorem actual_reducer_success_mod (w : U64) (z : U32)
    (h : AspisR1Qm31ArithmeticProbe.field.reduce_u64 w = .ok z) :
    z.val = w.val % AspisV8R17.RawReducer.P := by
  obtain ⟨out,hout,hmod,_hbound⟩ :=
    AspisR1.ExtractedCurrentReducer.current_reduce_mod w
  have heq : out = z := Result.ok.inj (hout.symm.trans h)
  simpa only [heq] using hmod

/-- Same returned output words and same actual input reads, with exact field
residues. No independent arithmetic or per-read success premise. -/
theorem generatedInnerN8_actualReducer_success_residues
    (ops : FourDotsOps)
    (limbs : fast_dots.four_dots.closure.closure)
    (values : Aeneas.Std.Array U32 8#usize)
    (h : (fourDotsOpsWithP6ArrayFromFnN8
        (fourDotsOpsWithActualReducer ops)).arrayFromFn 8#usize
      (fast_dots.four_dots.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU32
        (fourDotsOpsWithP6ArrayFromFnN8 (fourDotsOpsWithActualReducer ops)))
      limbs = .ok values) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 : U64),
      Array.index_usize limbs 0#usize = .ok w0 ∧
      Array.index_usize limbs 1#usize = .ok w1 ∧
      Array.index_usize limbs 2#usize = .ok w2 ∧
      Array.index_usize limbs 3#usize = .ok w3 ∧
      Array.index_usize limbs 4#usize = .ok w4 ∧
      Array.index_usize limbs 5#usize = .ok w5 ∧
      Array.index_usize limbs 6#usize = .ok w6 ∧
      Array.index_usize limbs 7#usize = .ok w7 ∧
      values.val.map (fun word => word.val) =
        [w0.val % AspisV8R17.RawReducer.P, w1.val % AspisV8R17.RawReducer.P,
         w2.val % AspisV8R17.RawReducer.P, w3.val % AspisV8R17.RawReducer.P,
         w4.val % AspisV8R17.RawReducer.P, w5.val % AspisV8R17.RawReducer.P,
         w6.val % AspisV8R17.RawReducer.P, w7.val % AspisV8R17.RawReducer.P] ∧
      (∀ value ∈ values.val, value.val < AspisV8R17.RawReducer.P) := by
  obtain ⟨m0,m1,m2,m3,m4,m5,m6,m7,w0,w1,w2,w3,w4,w5,w6,w7,
      hvalues,hi0,hr0,hi1,hr1,hi2,hr2,hi3,hr3,
      hi4,hr4,hi5,hr5,hi6,hr6,hi7,hr7⟩ :=
    generatedInnerN8ArrayField_success_values_match_fixedV6
      (fourDotsOpsWithActualReducer ops) limbs values h
  have hm0 := actual_reducer_success_mod w0 m0 hr0
  have hm1 := actual_reducer_success_mod w1 m1 hr1
  have hm2 := actual_reducer_success_mod w2 m2 hr2
  have hm3 := actual_reducer_success_mod w3 m3 hr3
  have hm4 := actual_reducer_success_mod w4 m4 hr4
  have hm5 := actual_reducer_success_mod w5 m5 hr5
  have hm6 := actual_reducer_success_mod w6 m6 hr6
  have hm7 := actual_reducer_success_mod w7 m7 hr7
  refine ⟨w0,w1,w2,w3,w4,w5,w6,w7,hi0,hi1,hi2,hi3,hi4,hi5,hi6,hi7,?_,?_⟩
  · simp only [hvalues,List.map_cons,List.map_nil,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7]
  · exact generatedInnerN8_actualReducer_success_canonical ops limbs values h

#print axioms actual_reducer_success_mod
#print axioms generatedInnerN8_actualReducer_success_residues
end AspisR1FromFnP6Generated
