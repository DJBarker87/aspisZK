import R0P.CoreExt

/-! Construct a `PackBasis` over the range of a field embedding from a
four-coordinate independence statement in the source field. -/

set_option autoImplicit false

namespace AspisR1.GenericPackBasis

theorem ofEmbedding {K E : Type} [Field K] [Field E]
    (e : K →+* E) (i u : E)
    (h_ind : ∀ a b c d : K,
      e a + i * e b + u * e c + i * u * e d = 0 →
        a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0) :
    R0P.PackBasis e.fieldRange := by
  refine ⟨i, u, ?_⟩
  intro a b c d ha hb hc hd hsum
  obtain ⟨a₀, ha₀⟩ := RingHom.mem_fieldRange.mp ha
  obtain ⟨b₀, hb₀⟩ := RingHom.mem_fieldRange.mp hb
  obtain ⟨c₀, hc₀⟩ := RingHom.mem_fieldRange.mp hc
  obtain ⟨d₀, hd₀⟩ := RingHom.mem_fieldRange.mp hd
  have hcoeff := h_ind a₀ b₀ c₀ d₀ (by
    rw [← ha₀, ← hb₀, ← hc₀, ← hd₀]
    exact hsum)
  rcases hcoeff with ⟨ha₀zero, hb₀zero, hc₀zero, hd₀zero⟩
  constructor
  · calc
      a = e a₀ := ha₀.symm
      _ = e 0 := by rw [ha₀zero]
      _ = 0 := map_zero _
  constructor
  · calc
      b = e b₀ := hb₀.symm
      _ = e 0 := by rw [hb₀zero]
      _ = 0 := map_zero _
  constructor
  · calc
      c = e c₀ := hc₀.symm
      _ = e 0 := by rw [hc₀zero]
      _ = 0 := map_zero _
  · calc
      d = e d₀ := hd₀.symm
      _ = e 0 := by rw [hd₀zero]
      _ = 0 := map_zero _

#print axioms ofEmbedding

end AspisR1.GenericPackBasis
