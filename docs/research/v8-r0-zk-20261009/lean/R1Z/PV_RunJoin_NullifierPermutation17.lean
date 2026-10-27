import R1Z.PV_RunJoin_NullifierData17
set_option autoImplicit false
namespace R1Z.PV_RunJoin_NullifierPermutation17
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep PV_RunJoin_NullifierData17

theorem state_injective (a b : State) (ha : Canonical a) (hb : Canonical b)
    (h : liftA (K := PV_RunJoin_FixtureRecords.M) a = liftA b) : a = b := by
  apply BuilderRecordCanonical.array_ext
  intro j hj
  have hlt : j < 16 := by simpa using hj
  apply PV_RunJoin_LeafLift16.word_injective (ha ⟨j,hlt⟩) (hb ⟨j,hlt⟩)
  exact congrFun h ⟨j,hlt⟩
#print axioms state_injective

theorem first : poseidon2.permute_optimized_with_trace_threaded
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_RunJoin_HashCallback17.callback s4_0 ((),0#usize) = ok (s4_23,((),0#usize)) := by
  obtain ⟨out,ho,hc,hm⟩ := PV_RunJoin_HashCallback17.permutation (K := PV_RunJoin_FixtureRecords.M) 0#usize s4_0
  rw [lift4_0,PV_RunJoin_FixtureHashModel.permutation_4] at hm
  have he : out = s4_23 := state_injective out s4_23 hc canon4_23 (hm.trans lift4_23.symm)
  exact ho.trans (congrArg Result.ok (congrArg (fun s => (s,((),0#usize))) he))
#print axioms first

theorem second : poseidon2.permute_optimized_with_trace_threaded
    (sourceExternalLinear := PV_Src_ExternalReference.dictionary)
    PV_RunJoin_HashCallback17.callback s5_0 ((),1#usize) = ok (s5_23,((),1#usize)) := by
  obtain ⟨out,ho,hc,hm⟩ := PV_RunJoin_HashCallback17.permutation (K := PV_RunJoin_FixtureRecords.M) 1#usize s5_0
  rw [lift5_0,PV_RunJoin_FixtureHashModel.permutation_5] at hm
  have he : out = s5_23 := state_injective out s5_23 hc canon5_23 (hm.trans lift5_23.symm)
  exact ho.trans (congrArg Result.ok (congrArg (fun s => (s,((),1#usize))) he))
#print axioms second
end R1Z.PV_RunJoin_NullifierPermutation17
