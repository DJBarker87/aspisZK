-- PCVN_ item (1) op2: the deployed from_le_bytes slot (NJC_ClosedCalls.inactive, the FIo_Native emission behind the retained coordinate port)
-- equals the fresh 4bb3b3f emission of WideExact.from_le_bytes (PRVFresh_R1CandidateWideParserSource_j1) behind the same structural port.
import Aeneas
import RPz7_FIo_Install
import NJC_ClosedCalls
import PRVEq_PCVH_R1CandidateWideParserSource_k1
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section
namespace PCVN_Op2

def port (x : AspisR1CandidateParser.field.wide_exact.WideExact) : AspisR1Stage2.Stage2Finish.E :=
  ⟨⟨⟨x.c0.c0.a, x.c0.c0.b⟩, ⟨x.c0.c1.a, x.c0.c1.b⟩⟩, ⟨⟨x.c1.c0.a, x.c1.c0.b⟩, ⟨x.c1.c1.a, x.c1.c1.b⟩⟩⟩

theorem P_eq : AspisR1CandidateParser.field.P = FIo_Native.aspis_core.field.P := by
  with_unfolding_all rfl

theorem op2_frozen (bytes : Slice Std.U8) :
    NJC_ClosedCalls.inactive bytes = (do
      let o ← AspisR1CandidateParser.PRVFresh_R1CandidateWideParserSource_j1.field.wide_exact.WideExact.from_le_bytes bytes
      ok (Option.map port o)) := by
  have h0 := congrFun PRVEq.R1CandidateWideParserSource_k1.field.wide_exact.WideExact.from_le_bytes bytes
  rw [h0]
  obtain ⟨l, hl⟩ := bytes
  by_cases h : l.length = 32
  · rcases l with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, _ | ⟨b9, _ | ⟨b10, _ | ⟨b11, _ | ⟨b12, _ | ⟨b13, _ | ⟨b14, _ | ⟨b15, _ | ⟨b16, _ | ⟨b17, _ | ⟨b18, _ | ⟨b19, _ | ⟨b20, _ | ⟨b21, _ | ⟨b22, _ | ⟨b23, _ | ⟨b24, _ | ⟨b25, _ | ⟨b26, _ | ⟨b27, _ | ⟨b28, _ | ⟨b29, _ | ⟨b30, _ | ⟨b31, _ | ⟨b32, tl⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> first | (exfalso; simp at h; done) | skip
    all_goals
      rw [PCVH.wide_eq b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 hl, PCVH.chain]
      rw [P_eq]
      unfold NJC_ClosedCalls.inactive NHV_InactivePacket.emitted
      simp [FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes, FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN, Slice.len, Slice.index_usize, Aeneas.Std.lift, FIo_Native.aspis_core.field.wide_exact.WideExact.from_limbs, Array.index_usize, Array.make, PCVH.lm, port, FIo_Install.fromE]
  · unfold NJC_ClosedCalls.inactive NHV_InactivePacket.emitted FIo_Native.aspis_core.field.wide_exact.WideExact.from_le_bytes AspisR1CandidateParser.field.wide_exact.WideExact.from_le_bytes
    simp [Slice.len, FIo_Native.aspis_core.field.wide_exact.WideExact.BYTE_LEN, AspisR1CandidateParser.field.wide_exact.WideExact.BYTE_LEN, h]

#print axioms op2_frozen
end PCVN_Op2
