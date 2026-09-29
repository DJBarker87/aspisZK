import AspisV8R19.QueryChunkModel

/-! The extracted inner query loop implements the retained finite word scan.
The source guard, actual 32-byte block chunking, outer loop and oracle law are
not premises silently supplied here: they remain separate obligations. -/
set_option autoImplicit false
namespace AspisV8R19.QueryChunkSource
open Aeneas Aeneas.Std Result AspisR86Query QueryChunkExecution QueryChunkModel

theorem source_scan_bounded (mask : U32) (ws : List Word) (rest : Slice U8)
    (out : Values) (draws : Usize) (hc : out.val.length ≤ 22) (hd : draws.val ≤ 64) :
    ∃ out1 draws1,
      transcript.Transcript.challenge_queries_without_replacement_loop0_loop0
        (chunks ws rest) 22#usize 64#usize mask out draws =
          .ok (out1,draws1,
            if (Q22WordScan.scan (view out draws) (candidates mask ws)).2 then 0#u32 else 1#u32) ∧
      view out1 draws1 = (Q22WordScan.scan (view out draws) (candidates mask ws)).1 ∧
      out1.val.length ≤ 22 ∧ draws1.val ≤ 64 := by
  obtain ⟨out1,draws1,he,hv⟩ := run_exact mask ws out draws hc hd
  refine ⟨out1,draws1,?_,hv,?_,?_⟩
  · simpa only [source_loop] using he
  · have h := Q22WordScan.scan_count_cap (view out draws) (candidates mask ws)
      (by simpa [view] using hc)
    rw [← hv] at h
    simpa [view] using h
  · have h := Q22WordScan.scan_draw_cap (view out draws) (candidates mask ws) hd
    rw [← hv] at h
    exact h

theorem continuing_consumes_all (mask : U32) (ws : List Word)
    (out : Values) (draws : Usize) (out1 : Values) (draws1 : Usize)
    (hv : view out1 draws1 = (Q22WordScan.scan (view out draws) (candidates mask ws)).1)
    (hcont : (Q22WordScan.scan (view out draws) (candidates mask ws)).2 = false) :
    draws1.val = draws.val + ws.length := by
  have h := Q22WordScan.scan_progress (view out draws) (candidates mask ws) hcont
  rw [← hv] at h
  simpa [view,candidates] using h

#print axioms source_scan_bounded
#print axioms continuing_consumes_all
end AspisV8R19.QueryChunkSource
