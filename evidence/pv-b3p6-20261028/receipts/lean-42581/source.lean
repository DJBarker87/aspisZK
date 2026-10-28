import PV_B3P_ChunkV3Law226
namespace PV_B3P_ChunkSuccess226V3
open Aeneas Aeneas.Std PV_B3P_226V3 PV_B3P_RustResult PV_B3P_ChunkV3Law226
set_option autoImplicit false

theorem success (p : reference226.OwnedPublic) (base : Usize)
    (h : ∀ j : Usize, ∃ v, reference226.byte_at p j = .ok (.Ok v)) :
    ∃ out, reference226.chunk8 p base = .ok (.Ok out) := by
  obtain ⟨b0,h0⟩ := h (Usize.wrapping_add base 0#usize)
  obtain ⟨b1,h1⟩ := h (Usize.wrapping_add base 1#usize)
  obtain ⟨b2,h2⟩ := h (Usize.wrapping_add base 2#usize)
  obtain ⟨b3,h3⟩ := h (Usize.wrapping_add base 3#usize)
  obtain ⟨b4,h4⟩ := h (Usize.wrapping_add base 4#usize)
  obtain ⟨b5,h5⟩ := h (Usize.wrapping_add base 5#usize)
  obtain ⟨b6,h6⟩ := h (Usize.wrapping_add base 6#usize)
  obtain ⟨b7,h7⟩ := h (Usize.wrapping_add base 7#usize)
  rw [complete_result]
  simp only [spec8,h0,h1,h2,h3,h4,h5,h6,h7,bindR]
  exact ⟨_,rfl⟩

#print axioms success
end PV_B3P_ChunkSuccess226V3
