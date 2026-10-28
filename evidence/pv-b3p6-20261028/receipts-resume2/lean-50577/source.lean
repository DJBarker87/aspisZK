import PV_B3P_ChunkSuccess226V3
import PV_B3P_Repeat226
namespace PV_B3P_Chunk64Success226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false
-- Same syntactic-depth allowance as the pinned 64-read emission. This proof
-- composes eight opaque byte chunks and 64 bounded reads, with no recurrence
-- or field arithmetic reduction.
set_option maxRecDepth 2048

theorem success (p : reference226.OwnedPublic) (base : Usize)
    (h : ∀ j : Usize, ∃ v, reference226.byte_at p j = .ok (.Ok v)) :
    ∃ out, reference226.chunk p base = .ok (.Ok out) := by
  obtain ⟨a0,h0⟩ := PV_B3P_ChunkSuccess226V3.success p
    (Usize.wrapping_add base 0#usize) h
  obtain ⟨a1,h1⟩ := PV_B3P_ChunkSuccess226V3.success p
    (Usize.wrapping_add base 8#usize) h
  obtain ⟨a2,h2⟩ := PV_B3P_ChunkSuccess226V3.success p
    (Usize.wrapping_add base 16#usize) h
  obtain ⟨a3,h3⟩ := PV_B3P_ChunkSuccess226V3.success p
    (Usize.wrapping_add base 24#usize) h
  obtain ⟨a4,h4⟩ := PV_B3P_ChunkSuccess226V3.success p
    (Usize.wrapping_add base 32#usize) h
  obtain ⟨a5,h5⟩ := PV_B3P_ChunkSuccess226V3.success p
    (Usize.wrapping_add base 40#usize) h
  obtain ⟨a6,h6⟩ := PV_B3P_ChunkSuccess226V3.success p
    (Usize.wrapping_add base 48#usize) h
  obtain ⟨a7,h7⟩ := PV_B3P_ChunkSuccess226V3.success p
    (Usize.wrapping_add base 56#usize) h
  unfold reference226.chunk
  simp only [lift,bind_tc_ok,h0,h1,h2,h3,h4,h5,h6,h7,
    core.result.Result.Insts.CoreOpsTry.branch]
  rw [PV_B3P_Repeat226.index_value a0 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a0 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a0 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a0 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a0 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a0 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a0 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a0 7#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a1 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a1 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a1 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a1 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a1 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a1 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a1 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a1 7#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a2 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a2 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a2 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a2 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a2 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a2 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a2 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a2 7#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a3 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a3 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a3 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a3 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a3 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a3 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a3 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a3 7#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a4 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a4 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a4 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a4 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a4 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a4 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a4 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a4 7#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a5 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a5 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a5 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a5 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a5 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a5 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a5 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a5 7#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a6 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a6 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a6 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a6 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a6 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a6 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a6 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a6 7#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a7 0#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a7 1#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a7 2#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a7 3#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a7 4#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a7 5#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a7 6#usize (by decide)]
  simp only [bind_tc_ok]
  rw [PV_B3P_Repeat226.index_value a7 7#usize (by decide)]
  simp only [bind_tc_ok]
  exact ⟨_,rfl⟩

#print axioms success
end PV_B3P_Chunk64Success226V3
