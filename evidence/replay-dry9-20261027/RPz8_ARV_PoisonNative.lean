import RPz8_ARV_Poison
set_option autoImplicit false
noncomputable section
namespace AspisR1.ARV_PoisonNative
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers

theorem accepted {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state final : A)
    (post : Heap (Nat → Record))
    (yes : second native allocator e id data slot state = ok (.Ok (post,final))) :
    second native allocator (ARV_Poison.entry e) id data slot state =
      ok (.Ok ((ARV_Poison.entry e).heap,final)) := by
  unfold second at yes ⊢
  obtain ⟨allocated,allocation,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ yes
  obtain ⟨result,called,rest⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
  cases result with
  | Err error => cases rest
  | Ok value =>
    obtain ⟨cleaned,cleanup,returned⟩ := AdapterRw.Cuts.bind_success _ _ _ rest
    have equal := core.result.Result.Ok.inj (Result.ok.inj returned)
    have finalEq : cleaned = final := congrArg Prod.snd equal
    simp only [ARV_Poison.sizes,ARV_Poison.owned,allocation,called,cleanup,bind_tc_ok]
    rw [finalEq]

#print axioms accepted
end AspisR1.ARV_PoisonNative
end
