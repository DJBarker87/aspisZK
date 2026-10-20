import AspisR1Query31Transcript.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section

namespace AspisR1Query31Transcript



/-- The unrolled candidate driver, with only its scanner made an explicit
operation parameter. Its finish body and all eight index/continuation branches
are copied from the generated candidate owner. -/
def queries_from_pairs_with_scan
  (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
  (scan0 : aspis_core.r0_transcript.QueryScan)
  (blocks : Array (Array Std.U8 32#usize) 8#usize)
  (advances : Array (Array Std.U8 32#usize) 8#usize) :
  Result (core.result.Result ((Array Std.U32 22#usize) × (Array Std.U8
    32#usize)) aspis_core.transcript.QuerySampleError)
  := do
  let scan := scan0
  let a ← Array.index_usize blocks 0#usize
  let (b, scan1) ← scanFn scan a
  if b
  then
    let r ← aspis_core.r0_transcript.QueryScan.finish scan1
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let a1 ← Array.index_usize advances 0#usize
      ok (core.result.Result.Ok (val, a1))
    | core.ops.control_flow.ControlFlow.Break residual =>
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
        ((Array Std.U32 22#usize) × (Array Std.U8 32#usize))
        (core.convert.FromSame aspis_core.transcript.QuerySampleError) residual
  else
    let a1 ← Array.index_usize blocks 1#usize
    let (b1, scan2) ← scanFn scan1 a1
    if b1
    then
      let r ← aspis_core.r0_transcript.QueryScan.finish scan2
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let a2 ← Array.index_usize advances 1#usize
        ok (core.result.Result.Ok (val, a2))
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          ((Array Std.U32 22#usize) × (Array Std.U8 32#usize))
          (core.convert.FromSame aspis_core.transcript.QuerySampleError)
          residual
    else
      let a2 ← Array.index_usize blocks 2#usize
      let (b2, scan3) ← scanFn scan2 a2
      if b2
      then
        let r ← aspis_core.r0_transcript.QueryScan.finish scan3
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let a3 ← Array.index_usize advances 2#usize
          ok (core.result.Result.Ok (val, a3))
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            ((Array Std.U32 22#usize) × (Array Std.U8 32#usize))
            (core.convert.FromSame aspis_core.transcript.QuerySampleError)
            residual
      else
        let a3 ← Array.index_usize blocks 3#usize
        let (b3, scan4) ← scanFn scan3 a3
        if b3
        then
          let r ← aspis_core.r0_transcript.QueryScan.finish scan4
          let cf ← core.result.Result.Insts.CoreOpsTry.branch r
          match cf with
          | core.ops.control_flow.ControlFlow.Continue val =>
            let a4 ← Array.index_usize advances 3#usize
            ok (core.result.Result.Ok (val, a4))
          | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              ((Array Std.U32 22#usize) × (Array Std.U8 32#usize))
              (core.convert.FromSame aspis_core.transcript.QuerySampleError)
              residual
        else
          let a4 ← Array.index_usize blocks 4#usize
          let (b4, scan5) ← scanFn scan4 a4
          if b4
          then
            let r ← aspis_core.r0_transcript.QueryScan.finish scan5
            let cf ← core.result.Result.Insts.CoreOpsTry.branch r
            match cf with
            | core.ops.control_flow.ControlFlow.Continue val =>
              let a5 ← Array.index_usize advances 4#usize
              ok (core.result.Result.Ok (val, a5))
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                ((Array Std.U32 22#usize) × (Array Std.U8 32#usize))
                (core.convert.FromSame aspis_core.transcript.QuerySampleError)
                residual
          else
            let a5 ← Array.index_usize blocks 5#usize
            let (b5, scan6) ←
              scanFn scan5 a5
            if b5
            then
              let r ← aspis_core.r0_transcript.QueryScan.finish scan6
              let cf ← core.result.Result.Insts.CoreOpsTry.branch r
              match cf with
              | core.ops.control_flow.ControlFlow.Continue val =>
                let a6 ← Array.index_usize advances 5#usize
                ok (core.result.Result.Ok (val, a6))
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  ((Array Std.U32 22#usize) × (Array Std.U8 32#usize))
                  (core.convert.FromSame
                  aspis_core.transcript.QuerySampleError) residual
            else
              let a6 ← Array.index_usize blocks 6#usize
              let (b6, scan7) ←
                scanFn scan6 a6
              if b6
              then
                let r ← aspis_core.r0_transcript.QueryScan.finish scan7
                let cf ← core.result.Result.Insts.CoreOpsTry.branch r
                match cf with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let a7 ← Array.index_usize advances 6#usize
                  ok (core.result.Result.Ok (val, a7))
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    ((Array Std.U32 22#usize) × (Array Std.U8 32#usize))
                    (core.convert.FromSame
                    aspis_core.transcript.QuerySampleError) residual
              else
                let a7 ← Array.index_usize blocks 7#usize
                let (_, scan8) ←
                  scanFn scan7 a7
                let r ← aspis_core.r0_transcript.QueryScan.finish scan8
                let cf ← core.result.Result.Insts.CoreOpsTry.branch r
                match cf with
                | core.ops.control_flow.ControlFlow.Continue val =>
                  let a8 ← Array.index_usize advances 7#usize
                  ok (core.result.Result.Ok (val, a8))
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    ((Array Std.U32 22#usize) × (Array Std.U8 32#usize))
                    (core.convert.FromSame
                    aspis_core.transcript.QuerySampleError) residual


/-- The emitted `finish` body succeeds exactly when all query slots are filled. -/
theorem finish_success_iff
    (s : aspis_core.r0_transcript.QueryScan)
    (accepted : Array Std.U32 22#usize) :
    aspis_core.r0_transcript.QueryScan.finish s =
      ok (core.result.Result.Ok accepted) ↔
      s.accepted_len = aspis_core.r0_transcript.QUERY_COUNT ∧
        accepted = s.accepted := by
  constructor
  · intro h
    by_cases hc : s.accepted_len = aspis_core.r0_transcript.QUERY_COUNT
    · simp [aspis_core.r0_transcript.QueryScan.finish, hc,
        aspis_core.r0_transcript.QUERY_COUNT] at h
      exact ⟨hc, h.symm⟩
    · have hc' : s.accepted_len ≠ 22#usize := by
        simpa [aspis_core.r0_transcript.QUERY_COUNT] using hc
      simp [aspis_core.r0_transcript.QueryScan.finish, hc',
        aspis_core.r0_transcript.QUERY_COUNT] at h
  · rintro ⟨hlen, haccepted⟩
    simp [aspis_core.r0_transcript.QueryScan.finish, hlen, haccepted,
      aspis_core.r0_transcript.QUERY_COUNT]

/-- First true stop at an early literal block selects that block's advance. -/
theorem queries_from_pairs_with_scan_stop0
    (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : aspis_core.r0_transcript.QueryScan)
    (s1 : aspis_core.r0_transcript.QueryScan)
    (b0 : Array Std.U8 32#usize)
    (next : Array Std.U8 32#usize)
    (accepted : Array Std.U32 22#usize)
    (hblock0 : Array.index_usize blocks 0#usize = ok b0)
    (hscan0 : scanFn s0 b0 = ok (true, s1))
    (hfinish0 : aspis_core.r0_transcript.QueryScan.finish s1 = ok (core.result.Result.Ok accepted))
    (hadvance0 : Array.index_usize advances 0#usize = ok next) :
    queries_from_pairs_with_scan scanFn s0 blocks advances =
      ok (core.result.Result.Ok (accepted, next)) := by
  simp [queries_from_pairs_with_scan, hblock0, hscan0, hfinish0, hadvance0, core.result.Result.Insts.CoreOpsTry.branch]

theorem queries_from_pairs_with_scan_stop1
    (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : aspis_core.r0_transcript.QueryScan)
    (s1 : aspis_core.r0_transcript.QueryScan)
    (s2 : aspis_core.r0_transcript.QueryScan)
    (b0 : Array Std.U8 32#usize)
    (b1 : Array Std.U8 32#usize)
    (next : Array Std.U8 32#usize)
    (accepted : Array Std.U32 22#usize)
    (hblock0 : Array.index_usize blocks 0#usize = ok b0)
    (hblock1 : Array.index_usize blocks 1#usize = ok b1)
    (hscan0 : scanFn s0 b0 = ok (false, s1))
    (hscan1 : scanFn s1 b1 = ok (true, s2))
    (hfinish1 : aspis_core.r0_transcript.QueryScan.finish s2 = ok (core.result.Result.Ok accepted))
    (hadvance1 : Array.index_usize advances 1#usize = ok next) :
    queries_from_pairs_with_scan scanFn s0 blocks advances =
      ok (core.result.Result.Ok (accepted, next)) := by
  simp [queries_from_pairs_with_scan, hblock0, hblock1, hscan0, hscan1, hfinish1, hadvance1, core.result.Result.Insts.CoreOpsTry.branch]

theorem queries_from_pairs_with_scan_stop2
    (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : aspis_core.r0_transcript.QueryScan)
    (s1 : aspis_core.r0_transcript.QueryScan)
    (s2 : aspis_core.r0_transcript.QueryScan)
    (s3 : aspis_core.r0_transcript.QueryScan)
    (b0 : Array Std.U8 32#usize)
    (b1 : Array Std.U8 32#usize)
    (b2 : Array Std.U8 32#usize)
    (next : Array Std.U8 32#usize)
    (accepted : Array Std.U32 22#usize)
    (hblock0 : Array.index_usize blocks 0#usize = ok b0)
    (hblock1 : Array.index_usize blocks 1#usize = ok b1)
    (hblock2 : Array.index_usize blocks 2#usize = ok b2)
    (hscan0 : scanFn s0 b0 = ok (false, s1))
    (hscan1 : scanFn s1 b1 = ok (false, s2))
    (hscan2 : scanFn s2 b2 = ok (true, s3))
    (hfinish2 : aspis_core.r0_transcript.QueryScan.finish s3 = ok (core.result.Result.Ok accepted))
    (hadvance2 : Array.index_usize advances 2#usize = ok next) :
    queries_from_pairs_with_scan scanFn s0 blocks advances =
      ok (core.result.Result.Ok (accepted, next)) := by
  simp [queries_from_pairs_with_scan, hblock0, hblock1, hblock2, hscan0, hscan1, hscan2, hfinish2, hadvance2, core.result.Result.Insts.CoreOpsTry.branch]

theorem queries_from_pairs_with_scan_stop3
    (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : aspis_core.r0_transcript.QueryScan)
    (s1 : aspis_core.r0_transcript.QueryScan)
    (s2 : aspis_core.r0_transcript.QueryScan)
    (s3 : aspis_core.r0_transcript.QueryScan)
    (s4 : aspis_core.r0_transcript.QueryScan)
    (b0 : Array Std.U8 32#usize)
    (b1 : Array Std.U8 32#usize)
    (b2 : Array Std.U8 32#usize)
    (b3 : Array Std.U8 32#usize)
    (next : Array Std.U8 32#usize)
    (accepted : Array Std.U32 22#usize)
    (hblock0 : Array.index_usize blocks 0#usize = ok b0)
    (hblock1 : Array.index_usize blocks 1#usize = ok b1)
    (hblock2 : Array.index_usize blocks 2#usize = ok b2)
    (hblock3 : Array.index_usize blocks 3#usize = ok b3)
    (hscan0 : scanFn s0 b0 = ok (false, s1))
    (hscan1 : scanFn s1 b1 = ok (false, s2))
    (hscan2 : scanFn s2 b2 = ok (false, s3))
    (hscan3 : scanFn s3 b3 = ok (true, s4))
    (hfinish3 : aspis_core.r0_transcript.QueryScan.finish s4 = ok (core.result.Result.Ok accepted))
    (hadvance3 : Array.index_usize advances 3#usize = ok next) :
    queries_from_pairs_with_scan scanFn s0 blocks advances =
      ok (core.result.Result.Ok (accepted, next)) := by
  simp [queries_from_pairs_with_scan, hblock0, hblock1, hblock2, hblock3, hscan0, hscan1, hscan2, hscan3, hfinish3, hadvance3, core.result.Result.Insts.CoreOpsTry.branch]

theorem queries_from_pairs_with_scan_stop4
    (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : aspis_core.r0_transcript.QueryScan)
    (s1 : aspis_core.r0_transcript.QueryScan)
    (s2 : aspis_core.r0_transcript.QueryScan)
    (s3 : aspis_core.r0_transcript.QueryScan)
    (s4 : aspis_core.r0_transcript.QueryScan)
    (s5 : aspis_core.r0_transcript.QueryScan)
    (b0 : Array Std.U8 32#usize)
    (b1 : Array Std.U8 32#usize)
    (b2 : Array Std.U8 32#usize)
    (b3 : Array Std.U8 32#usize)
    (b4 : Array Std.U8 32#usize)
    (next : Array Std.U8 32#usize)
    (accepted : Array Std.U32 22#usize)
    (hblock0 : Array.index_usize blocks 0#usize = ok b0)
    (hblock1 : Array.index_usize blocks 1#usize = ok b1)
    (hblock2 : Array.index_usize blocks 2#usize = ok b2)
    (hblock3 : Array.index_usize blocks 3#usize = ok b3)
    (hblock4 : Array.index_usize blocks 4#usize = ok b4)
    (hscan0 : scanFn s0 b0 = ok (false, s1))
    (hscan1 : scanFn s1 b1 = ok (false, s2))
    (hscan2 : scanFn s2 b2 = ok (false, s3))
    (hscan3 : scanFn s3 b3 = ok (false, s4))
    (hscan4 : scanFn s4 b4 = ok (true, s5))
    (hfinish4 : aspis_core.r0_transcript.QueryScan.finish s5 = ok (core.result.Result.Ok accepted))
    (hadvance4 : Array.index_usize advances 4#usize = ok next) :
    queries_from_pairs_with_scan scanFn s0 blocks advances =
      ok (core.result.Result.Ok (accepted, next)) := by
  simp [queries_from_pairs_with_scan, hblock0, hblock1, hblock2, hblock3, hblock4, hscan0, hscan1, hscan2, hscan3, hscan4, hfinish4, hadvance4, core.result.Result.Insts.CoreOpsTry.branch]

theorem queries_from_pairs_with_scan_stop5
    (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : aspis_core.r0_transcript.QueryScan)
    (s1 : aspis_core.r0_transcript.QueryScan)
    (s2 : aspis_core.r0_transcript.QueryScan)
    (s3 : aspis_core.r0_transcript.QueryScan)
    (s4 : aspis_core.r0_transcript.QueryScan)
    (s5 : aspis_core.r0_transcript.QueryScan)
    (s6 : aspis_core.r0_transcript.QueryScan)
    (b0 : Array Std.U8 32#usize)
    (b1 : Array Std.U8 32#usize)
    (b2 : Array Std.U8 32#usize)
    (b3 : Array Std.U8 32#usize)
    (b4 : Array Std.U8 32#usize)
    (b5 : Array Std.U8 32#usize)
    (next : Array Std.U8 32#usize)
    (accepted : Array Std.U32 22#usize)
    (hblock0 : Array.index_usize blocks 0#usize = ok b0)
    (hblock1 : Array.index_usize blocks 1#usize = ok b1)
    (hblock2 : Array.index_usize blocks 2#usize = ok b2)
    (hblock3 : Array.index_usize blocks 3#usize = ok b3)
    (hblock4 : Array.index_usize blocks 4#usize = ok b4)
    (hblock5 : Array.index_usize blocks 5#usize = ok b5)
    (hscan0 : scanFn s0 b0 = ok (false, s1))
    (hscan1 : scanFn s1 b1 = ok (false, s2))
    (hscan2 : scanFn s2 b2 = ok (false, s3))
    (hscan3 : scanFn s3 b3 = ok (false, s4))
    (hscan4 : scanFn s4 b4 = ok (false, s5))
    (hscan5 : scanFn s5 b5 = ok (true, s6))
    (hfinish5 : aspis_core.r0_transcript.QueryScan.finish s6 = ok (core.result.Result.Ok accepted))
    (hadvance5 : Array.index_usize advances 5#usize = ok next) :
    queries_from_pairs_with_scan scanFn s0 blocks advances =
      ok (core.result.Result.Ok (accepted, next)) := by
  simp [queries_from_pairs_with_scan, hblock0, hblock1, hblock2, hblock3, hblock4, hblock5, hscan0, hscan1, hscan2, hscan3, hscan4, hscan5, hfinish5, hadvance5, core.result.Result.Insts.CoreOpsTry.branch]

theorem queries_from_pairs_with_scan_stop6
    (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : aspis_core.r0_transcript.QueryScan)
    (s1 : aspis_core.r0_transcript.QueryScan)
    (s2 : aspis_core.r0_transcript.QueryScan)
    (s3 : aspis_core.r0_transcript.QueryScan)
    (s4 : aspis_core.r0_transcript.QueryScan)
    (s5 : aspis_core.r0_transcript.QueryScan)
    (s6 : aspis_core.r0_transcript.QueryScan)
    (s7 : aspis_core.r0_transcript.QueryScan)
    (b0 : Array Std.U8 32#usize)
    (b1 : Array Std.U8 32#usize)
    (b2 : Array Std.U8 32#usize)
    (b3 : Array Std.U8 32#usize)
    (b4 : Array Std.U8 32#usize)
    (b5 : Array Std.U8 32#usize)
    (b6 : Array Std.U8 32#usize)
    (next : Array Std.U8 32#usize)
    (accepted : Array Std.U32 22#usize)
    (hblock0 : Array.index_usize blocks 0#usize = ok b0)
    (hblock1 : Array.index_usize blocks 1#usize = ok b1)
    (hblock2 : Array.index_usize blocks 2#usize = ok b2)
    (hblock3 : Array.index_usize blocks 3#usize = ok b3)
    (hblock4 : Array.index_usize blocks 4#usize = ok b4)
    (hblock5 : Array.index_usize blocks 5#usize = ok b5)
    (hblock6 : Array.index_usize blocks 6#usize = ok b6)
    (hscan0 : scanFn s0 b0 = ok (false, s1))
    (hscan1 : scanFn s1 b1 = ok (false, s2))
    (hscan2 : scanFn s2 b2 = ok (false, s3))
    (hscan3 : scanFn s3 b3 = ok (false, s4))
    (hscan4 : scanFn s4 b4 = ok (false, s5))
    (hscan5 : scanFn s5 b5 = ok (false, s6))
    (hscan6 : scanFn s6 b6 = ok (true, s7))
    (hfinish6 : aspis_core.r0_transcript.QueryScan.finish s7 = ok (core.result.Result.Ok accepted))
    (hadvance6 : Array.index_usize advances 6#usize = ok next) :
    queries_from_pairs_with_scan scanFn s0 blocks advances =
      ok (core.result.Result.Ok (accepted, next)) := by
  simp [queries_from_pairs_with_scan, hblock0, hblock1, hblock2, hblock3, hblock4, hblock5, hblock6, hscan0, hscan1, hscan2, hscan3, hscan4, hscan5, hscan6, hfinish6, hadvance6, core.result.Result.Insts.CoreOpsTry.branch]

theorem queries_from_pairs_with_scan_stop7
    (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : aspis_core.r0_transcript.QueryScan)
    (s1 : aspis_core.r0_transcript.QueryScan)
    (s2 : aspis_core.r0_transcript.QueryScan)
    (s3 : aspis_core.r0_transcript.QueryScan)
    (s4 : aspis_core.r0_transcript.QueryScan)
    (s5 : aspis_core.r0_transcript.QueryScan)
    (s6 : aspis_core.r0_transcript.QueryScan)
    (s7 : aspis_core.r0_transcript.QueryScan)
    (s8 : aspis_core.r0_transcript.QueryScan)
    (b0 : Array Std.U8 32#usize)
    (b1 : Array Std.U8 32#usize)
    (b2 : Array Std.U8 32#usize)
    (b3 : Array Std.U8 32#usize)
    (b4 : Array Std.U8 32#usize)
    (b5 : Array Std.U8 32#usize)
    (b6 : Array Std.U8 32#usize)
    (b7 : Array Std.U8 32#usize)
    (next : Array Std.U8 32#usize)
    (accepted : Array Std.U32 22#usize)
    (hblock0 : Array.index_usize blocks 0#usize = ok b0)
    (hblock1 : Array.index_usize blocks 1#usize = ok b1)
    (hblock2 : Array.index_usize blocks 2#usize = ok b2)
    (hblock3 : Array.index_usize blocks 3#usize = ok b3)
    (hblock4 : Array.index_usize blocks 4#usize = ok b4)
    (hblock5 : Array.index_usize blocks 5#usize = ok b5)
    (hblock6 : Array.index_usize blocks 6#usize = ok b6)
    (hblock7 : Array.index_usize blocks 7#usize = ok b7)
    (hscan0 : scanFn s0 b0 = ok (false, s1))
    (hscan1 : scanFn s1 b1 = ok (false, s2))
    (hscan2 : scanFn s2 b2 = ok (false, s3))
    (hscan3 : scanFn s3 b3 = ok (false, s4))
    (hscan4 : scanFn s4 b4 = ok (false, s5))
    (hscan5 : scanFn s5 b5 = ok (false, s6))
    (hscan6 : scanFn s6 b6 = ok (false, s7))
    (lastStop : Bool)
    (hscan7 : scanFn s7 b7 = ok (lastStop, s8))
    (hfinish7 : aspis_core.r0_transcript.QueryScan.finish s8 = ok (core.result.Result.Ok accepted))
    (hadvance7 : Array.index_usize advances 7#usize = ok next) :
    queries_from_pairs_with_scan scanFn s0 blocks advances =
      ok (core.result.Result.Ok (accepted, next)) := by
  simp [queries_from_pairs_with_scan, hblock0, hblock1, hblock2, hblock3, hblock4, hblock5, hblock6, hblock7, hscan0, hscan1, hscan2, hscan3, hscan4, hscan5, hscan6, hscan7, hfinish7, hadvance7, core.result.Result.Insts.CoreOpsTry.branch]

#print axioms queries_from_pairs_with_scan_stop0
#print axioms queries_from_pairs_with_scan_stop1
#print axioms queries_from_pairs_with_scan_stop2
#print axioms queries_from_pairs_with_scan_stop3
#print axioms queries_from_pairs_with_scan_stop4
#print axioms queries_from_pairs_with_scan_stop5
#print axioms queries_from_pairs_with_scan_stop6
#print axioms queries_from_pairs_with_scan_stop7
#print axioms finish_success_iff
end AspisR1Query31Transcript
