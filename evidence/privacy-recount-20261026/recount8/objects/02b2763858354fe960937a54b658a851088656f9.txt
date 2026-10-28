import PV_B3P_ChunkV3Law226
namespace PV_B3P_Chunk8Outcome226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult PV_B3P_ChunkV3Law226
set_option autoImplicit false

theorem no_outer_failure (p : reference226.OwnedPublic) (base : Usize)
    (h : ∀ j : Usize, ∃ r, reference226.byte_at p j = .ok r) :
    ∃ r, reference226.chunk8 p base = .ok r := by
  rw [complete_result]
  unfold spec8
  obtain ⟨r0,h0⟩ := h (Usize.wrapping_add base 0#usize)
  rw [h0]
  cases r0 with
  | Err e => exact ⟨.Err e,rfl⟩
  | Ok b0 =>
    simp only [bindR]
    obtain ⟨r1,h1⟩ := h (Usize.wrapping_add base 1#usize)
    rw [h1]
    cases r1 with
    | Err e => exact ⟨.Err e,rfl⟩
    | Ok b1 =>
      simp only [bindR]
      obtain ⟨r2,h2⟩ := h (Usize.wrapping_add base 2#usize)
      rw [h2]
      cases r2 with
      | Err e => exact ⟨.Err e,rfl⟩
      | Ok b2 =>
        simp only [bindR]
        obtain ⟨r3,h3⟩ := h (Usize.wrapping_add base 3#usize)
        rw [h3]
        cases r3 with
        | Err e => exact ⟨.Err e,rfl⟩
        | Ok b3 =>
          simp only [bindR]
          obtain ⟨r4,h4⟩ := h (Usize.wrapping_add base 4#usize)
          rw [h4]
          cases r4 with
          | Err e => exact ⟨.Err e,rfl⟩
          | Ok b4 =>
            simp only [bindR]
            obtain ⟨r5,h5⟩ := h (Usize.wrapping_add base 5#usize)
            rw [h5]
            cases r5 with
            | Err e => exact ⟨.Err e,rfl⟩
            | Ok b5 =>
              simp only [bindR]
              obtain ⟨r6,h6⟩ := h (Usize.wrapping_add base 6#usize)
              rw [h6]
              cases r6 with
              | Err e => exact ⟨.Err e,rfl⟩
              | Ok b6 =>
                simp only [bindR]
                obtain ⟨r7,h7⟩ := h (Usize.wrapping_add base 7#usize)
                rw [h7]
                cases r7 with
                | Err e => exact ⟨.Err e,rfl⟩
                | Ok b7 =>
                  simp only [bindR]
                  exact ⟨_,rfl⟩

#print axioms no_outer_failure
end PV_B3P_Chunk8Outcome226V3
