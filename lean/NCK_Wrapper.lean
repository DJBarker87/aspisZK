import S2W_D189Wrappers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NCK_Wrapper
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry
open S2W_D189Wrappers
/-- Forward composition on the SAME entry and actual allocator continuation.
This is only the wrapper edge; native acceptance is not discharged here. -/
theorem second_of_cuts {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (program : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state allocated final : A)
    (allocation : reserve allocator (admittedSizes e 7 secondSizes) state = ok allocated)
    (body : native program (e.second secondSizes) data slot = ok (.Ok ()))
    (cleanup : allocator.cleanup allocated = ok final) :
    second native allocator e program data slot state = ok (.Ok (e.heap,final)) := by
  simp only [second, allocation, bind_tc_ok, body, cleanup]

/-- The successful wrapper has exactly allocation, body and cleanup cuts.
No final heap or independently chosen body run is introduced as a premise. -/
theorem second_iff {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (program : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state final : A) :
    second native allocator e program data slot state = ok (.Ok (e.heap,final)) ↔
      ∃ allocated,
        reserve allocator (admittedSizes e 7 secondSizes) state = ok allocated ∧
        native program (e.second secondSizes) data slot = ok (.Ok ()) ∧
        allocator.cleanup allocated = ok final := by
  constructor
  · intro accepted
    unfold second at accepted
    obtain ⟨allocated,allocation,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ accepted
    obtain ⟨result,called,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
    cases result with
    | Err error => cases rest
    | Ok value =>
      obtain ⟨cleaned,cleanup,returned⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
      have equal := core.result.Result.Ok.inj (Result.ok.inj returned)
      have last : cleaned = final := congrArg Prod.snd equal
      subst cleaned
      exact ⟨allocated,allocation,called,cleanup⟩
  · rintro ⟨allocated,allocation,body,cleanup⟩
    exact second_of_cuts native allocator e program data slot state allocated final allocation body cleanup
#print axioms second_of_cuts
#print axioms second_iff
end AspisR1.NCK_Wrapper
end
