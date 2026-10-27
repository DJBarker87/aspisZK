import RPx_Fresh
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_Duplicates
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

theorem append_mono (before after : List (Bytes × State)) :
    firstReads emptyTable before≤firstReads emptyTable (before++after) := by
  classical
  rw [AllAddressCollisionTrace.firstReads_eq_card_finiteSupport,
    AllAddressCollisionTrace.firstReads_eq_card_finiteSupport]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨mem,empty⟩ := Finset.mem_filter.mp ha
  apply Finset.mem_filter.mpr
  refine ⟨?_,empty⟩
  simpa only [List.map_append,List.toFinset_append,Finset.mem_union] using Or.inl mem

/-- A repeated suffix is free ONLY in first-read accounting. It still adds
its full occurrence count to the log. -/
theorem repeated (before replay : List (Bytes × State)) :
    firstReads emptyTable ((before++replay)++replay)=firstReads emptyTable (before++replay) ∧
    ((before++replay)++replay).length=(before++replay).length+replay.length :=
  ⟨OracleProgramRecording.firstReads_repeat_suffix before replay,List.length_append⟩

#print axioms append_mono
#print axioms repeated
end AspisR1.RPx_Duplicates
end
