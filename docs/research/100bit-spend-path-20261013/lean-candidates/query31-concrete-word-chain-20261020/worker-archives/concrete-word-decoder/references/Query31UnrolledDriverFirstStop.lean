import Query31ScanTypesOnly
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
noncomputable section

namespace AspisR1Query31Transcript

@[global_simps, irreducible]
def aspis_core.r0_transcript.QUERY_COUNT : Std.Usize := 22#usize

@[global_simps, irreducible]
def aspis_core.r0_transcript.QUERY_MAX_DRAWS : Std.Usize := 64#usize

def aspis_core.r0_transcript.QueryScan.finish
  (self : aspis_core.r0_transcript.QueryScan) :
  Result (core.result.Result (Array Std.U32 22#usize)
    aspis_core.transcript.QuerySampleError)
  := do
  if self.accepted_len = aspis_core.r0_transcript.QUERY_COUNT
  then ok (core.result.Result.Ok self.accepted)
  else
    ok (core.result.Result.Err
      (aspis_core.transcript.QuerySampleError.DrawLimitExhausted
      self.accepted_len aspis_core.r0_transcript.QUERY_MAX_DRAWS))

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a,b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a,b) ∧ k a b = ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a,b,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

def finishAdvance
    (advances : Array (Array Std.U8 32#usize) 8#usize)
    (index : Std.Usize) (s : aspis_core.r0_transcript.QueryScan) :
    Result (core.result.Result ((Array Std.U32 22#usize) × (Array Std.U8 32#usize))
      aspis_core.transcript.QuerySampleError) := do
  let r ← aspis_core.r0_transcript.QueryScan.finish s
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | core.ops.control_flow.ControlFlow.Continue val =>
    let a ← Array.index_usize advances index
    ok (core.result.Result.Ok (val, a))
  | core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      ((Array Std.U32 22#usize) × (Array Std.U8 32#usize))
      (core.convert.FromSame aspis_core.transcript.QuerySampleError) residual

theorem finishAdvance_success
    (advances : Array (Array Std.U8 32#usize) 8#usize)
    (index : Std.Usize) (s : aspis_core.r0_transcript.QueryScan)
    (accepted : Array Std.U32 22#usize) (next : Array Std.U8 32#usize)
    (h : finishAdvance advances index s = ok (core.result.Result.Ok (accepted, next))) :
    aspis_core.r0_transcript.QueryScan.finish s =
        ok (core.result.Result.Ok accepted) ∧
      Array.index_usize advances index = ok next := by
  unfold finishAdvance at h
  obtain ⟨finished, hfinish, htail⟩ := bind_success
    (aspis_core.r0_transcript.QueryScan.finish s) _ _ h
  cases finished with
  | Ok value =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at htail
    obtain ⟨a, hadvance, hpair⟩ := bind_success
      (Array.index_usize advances index) _ _ htail
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hpair
    rcases hpair with ⟨rfl, rfl⟩
    exact ⟨hfinish, hadvance⟩
  | Err e =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at htail

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


inductive DriverTrace
    (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (s0 : aspis_core.r0_transcript.QueryScan)
    (accepted : Array Std.U32 22#usize) (next : Array Std.U8 32#usize) : Prop where
  | stop0
      (b0 : Array Std.U8 32#usize) (s1 : aspis_core.r0_transcript.QueryScan)
      (hblock0 : Array.index_usize blocks 0#usize = ok b0)
      (hscan0 : scanFn s0 b0 = ok (true, s1))
      (hfinish : aspis_core.r0_transcript.QueryScan.finish s1 = ok (core.result.Result.Ok accepted))
      (hadvance : Array.index_usize advances 0#usize = ok next) :
      DriverTrace scanFn blocks advances s0 accepted next
  | stop1
      (b0 : Array Std.U8 32#usize) (s1 : aspis_core.r0_transcript.QueryScan)
      (b1 : Array Std.U8 32#usize) (s2 : aspis_core.r0_transcript.QueryScan)
      (hblock0 : Array.index_usize blocks 0#usize = ok b0)
      (hblock1 : Array.index_usize blocks 1#usize = ok b1)
      (hscan0 : scanFn s0 b0 = ok (false, s1))
      (hscan1 : scanFn s1 b1 = ok (true, s2))
      (hfinish : aspis_core.r0_transcript.QueryScan.finish s2 = ok (core.result.Result.Ok accepted))
      (hadvance : Array.index_usize advances 1#usize = ok next) :
      DriverTrace scanFn blocks advances s0 accepted next
  | stop2
      (b0 : Array Std.U8 32#usize) (s1 : aspis_core.r0_transcript.QueryScan)
      (b1 : Array Std.U8 32#usize) (s2 : aspis_core.r0_transcript.QueryScan)
      (b2 : Array Std.U8 32#usize) (s3 : aspis_core.r0_transcript.QueryScan)
      (hblock0 : Array.index_usize blocks 0#usize = ok b0)
      (hblock1 : Array.index_usize blocks 1#usize = ok b1)
      (hblock2 : Array.index_usize blocks 2#usize = ok b2)
      (hscan0 : scanFn s0 b0 = ok (false, s1))
      (hscan1 : scanFn s1 b1 = ok (false, s2))
      (hscan2 : scanFn s2 b2 = ok (true, s3))
      (hfinish : aspis_core.r0_transcript.QueryScan.finish s3 = ok (core.result.Result.Ok accepted))
      (hadvance : Array.index_usize advances 2#usize = ok next) :
      DriverTrace scanFn blocks advances s0 accepted next
  | stop3
      (b0 : Array Std.U8 32#usize) (s1 : aspis_core.r0_transcript.QueryScan)
      (b1 : Array Std.U8 32#usize) (s2 : aspis_core.r0_transcript.QueryScan)
      (b2 : Array Std.U8 32#usize) (s3 : aspis_core.r0_transcript.QueryScan)
      (b3 : Array Std.U8 32#usize) (s4 : aspis_core.r0_transcript.QueryScan)
      (hblock0 : Array.index_usize blocks 0#usize = ok b0)
      (hblock1 : Array.index_usize blocks 1#usize = ok b1)
      (hblock2 : Array.index_usize blocks 2#usize = ok b2)
      (hblock3 : Array.index_usize blocks 3#usize = ok b3)
      (hscan0 : scanFn s0 b0 = ok (false, s1))
      (hscan1 : scanFn s1 b1 = ok (false, s2))
      (hscan2 : scanFn s2 b2 = ok (false, s3))
      (hscan3 : scanFn s3 b3 = ok (true, s4))
      (hfinish : aspis_core.r0_transcript.QueryScan.finish s4 = ok (core.result.Result.Ok accepted))
      (hadvance : Array.index_usize advances 3#usize = ok next) :
      DriverTrace scanFn blocks advances s0 accepted next
  | stop4
      (b0 : Array Std.U8 32#usize) (s1 : aspis_core.r0_transcript.QueryScan)
      (b1 : Array Std.U8 32#usize) (s2 : aspis_core.r0_transcript.QueryScan)
      (b2 : Array Std.U8 32#usize) (s3 : aspis_core.r0_transcript.QueryScan)
      (b3 : Array Std.U8 32#usize) (s4 : aspis_core.r0_transcript.QueryScan)
      (b4 : Array Std.U8 32#usize) (s5 : aspis_core.r0_transcript.QueryScan)
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
      (hfinish : aspis_core.r0_transcript.QueryScan.finish s5 = ok (core.result.Result.Ok accepted))
      (hadvance : Array.index_usize advances 4#usize = ok next) :
      DriverTrace scanFn blocks advances s0 accepted next
  | stop5
      (b0 : Array Std.U8 32#usize) (s1 : aspis_core.r0_transcript.QueryScan)
      (b1 : Array Std.U8 32#usize) (s2 : aspis_core.r0_transcript.QueryScan)
      (b2 : Array Std.U8 32#usize) (s3 : aspis_core.r0_transcript.QueryScan)
      (b3 : Array Std.U8 32#usize) (s4 : aspis_core.r0_transcript.QueryScan)
      (b4 : Array Std.U8 32#usize) (s5 : aspis_core.r0_transcript.QueryScan)
      (b5 : Array Std.U8 32#usize) (s6 : aspis_core.r0_transcript.QueryScan)
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
      (hfinish : aspis_core.r0_transcript.QueryScan.finish s6 = ok (core.result.Result.Ok accepted))
      (hadvance : Array.index_usize advances 5#usize = ok next) :
      DriverTrace scanFn blocks advances s0 accepted next
  | stop6
      (b0 : Array Std.U8 32#usize) (s1 : aspis_core.r0_transcript.QueryScan)
      (b1 : Array Std.U8 32#usize) (s2 : aspis_core.r0_transcript.QueryScan)
      (b2 : Array Std.U8 32#usize) (s3 : aspis_core.r0_transcript.QueryScan)
      (b3 : Array Std.U8 32#usize) (s4 : aspis_core.r0_transcript.QueryScan)
      (b4 : Array Std.U8 32#usize) (s5 : aspis_core.r0_transcript.QueryScan)
      (b5 : Array Std.U8 32#usize) (s6 : aspis_core.r0_transcript.QueryScan)
      (b6 : Array Std.U8 32#usize) (s7 : aspis_core.r0_transcript.QueryScan)
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
      (hfinish : aspis_core.r0_transcript.QueryScan.finish s7 = ok (core.result.Result.Ok accepted))
      (hadvance : Array.index_usize advances 6#usize = ok next) :
      DriverTrace scanFn blocks advances s0 accepted next
  | stop7
      (b0 : Array Std.U8 32#usize) (s1 : aspis_core.r0_transcript.QueryScan)
      (b1 : Array Std.U8 32#usize) (s2 : aspis_core.r0_transcript.QueryScan)
      (b2 : Array Std.U8 32#usize) (s3 : aspis_core.r0_transcript.QueryScan)
      (b3 : Array Std.U8 32#usize) (s4 : aspis_core.r0_transcript.QueryScan)
      (b4 : Array Std.U8 32#usize) (s5 : aspis_core.r0_transcript.QueryScan)
      (b5 : Array Std.U8 32#usize) (s6 : aspis_core.r0_transcript.QueryScan)
      (b6 : Array Std.U8 32#usize) (s7 : aspis_core.r0_transcript.QueryScan)
      (b7 : Array Std.U8 32#usize) (s8 : aspis_core.r0_transcript.QueryScan)
      (lastStop : Bool)
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
      (hscan7 : scanFn s7 b7 = ok (lastStop, s8))
      (hfinish : aspis_core.r0_transcript.QueryScan.finish s8 = ok (core.result.Result.Ok accepted))
      (hadvance : Array.index_usize advances 7#usize = ok next) :
      DriverTrace scanFn blocks advances s0 accepted next

theorem successful_driver_has_trace
    (scanFn : aspis_core.r0_transcript.QueryScan → Array Std.U8 32#usize → Result (Bool × aspis_core.r0_transcript.QueryScan))
    (scan0 : aspis_core.r0_transcript.QueryScan)
    (blocks advances : Array (Array Std.U8 32#usize) 8#usize)
    (accepted : Array Std.U32 22#usize) (next : Array Std.U8 32#usize)
    (h : queries_from_pairs_with_scan scanFn scan0 blocks advances =
      ok (core.result.Result.Ok (accepted, next))) :
    DriverTrace scanFn blocks advances scan0 accepted next := by
  unfold queries_from_pairs_with_scan at h
  obtain ⟨b0, hblock0, h⟩ := bind_success _ _ _ h
  obtain ⟨stop0, s1, hscan0, h⟩ := pair_bind_success _ _ _ h
  cases stop0 with
  | true =>
      change finishAdvance advances 0#usize s1 = _ at h
      have hf := finishAdvance_success advances 0#usize s1 accepted next h
      exact DriverTrace.stop0 b0 s1 hblock0 hscan0 hf.1 hf.2
  | false =>
  obtain ⟨b1, hblock1, h⟩ := bind_success _ _ _ h
  obtain ⟨stop1, s2, hscan1, h⟩ := pair_bind_success _ _ _ h
  cases stop1 with
  | true =>
      change finishAdvance advances 1#usize s2 = _ at h
      have hf := finishAdvance_success advances 1#usize s2 accepted next h
      exact DriverTrace.stop1 b0 s1 b1 s2 hblock0 hblock1 hscan0 hscan1 hf.1 hf.2
  | false =>
  obtain ⟨b2, hblock2, h⟩ := bind_success _ _ _ h
  obtain ⟨stop2, s3, hscan2, h⟩ := pair_bind_success _ _ _ h
  cases stop2 with
  | true =>
      change finishAdvance advances 2#usize s3 = _ at h
      have hf := finishAdvance_success advances 2#usize s3 accepted next h
      exact DriverTrace.stop2 b0 s1 b1 s2 b2 s3 hblock0 hblock1 hblock2 hscan0 hscan1 hscan2 hf.1 hf.2
  | false =>
  obtain ⟨b3, hblock3, h⟩ := bind_success _ _ _ h
  obtain ⟨stop3, s4, hscan3, h⟩ := pair_bind_success _ _ _ h
  cases stop3 with
  | true =>
      change finishAdvance advances 3#usize s4 = _ at h
      have hf := finishAdvance_success advances 3#usize s4 accepted next h
      exact DriverTrace.stop3 b0 s1 b1 s2 b2 s3 b3 s4 hblock0 hblock1 hblock2 hblock3 hscan0 hscan1 hscan2 hscan3 hf.1 hf.2
  | false =>
  obtain ⟨b4, hblock4, h⟩ := bind_success _ _ _ h
  obtain ⟨stop4, s5, hscan4, h⟩ := pair_bind_success _ _ _ h
  cases stop4 with
  | true =>
      change finishAdvance advances 4#usize s5 = _ at h
      have hf := finishAdvance_success advances 4#usize s5 accepted next h
      exact DriverTrace.stop4 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 hblock0 hblock1 hblock2 hblock3 hblock4 hscan0 hscan1 hscan2 hscan3 hscan4 hf.1 hf.2
  | false =>
  obtain ⟨b5, hblock5, h⟩ := bind_success _ _ _ h
  obtain ⟨stop5, s6, hscan5, h⟩ := pair_bind_success _ _ _ h
  cases stop5 with
  | true =>
      change finishAdvance advances 5#usize s6 = _ at h
      have hf := finishAdvance_success advances 5#usize s6 accepted next h
      exact DriverTrace.stop5 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hf.1 hf.2
  | false =>
  obtain ⟨b6, hblock6, h⟩ := bind_success _ _ _ h
  obtain ⟨stop6, s7, hscan6, h⟩ := pair_bind_success _ _ _ h
  cases stop6 with
  | true =>
      change finishAdvance advances 6#usize s7 = _ at h
      have hf := finishAdvance_success advances 6#usize s7 accepted next h
      exact DriverTrace.stop6 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hf.1 hf.2
  | false =>
  obtain ⟨b7, hblock7, h⟩ := bind_success _ _ _ h
  obtain ⟨stop7, s8, hscan7, h⟩ := pair_bind_success _ _ _ h
  have hf := finishAdvance_success advances 7#usize s8 accepted next (by
    change finishAdvance advances 7#usize s8 = _
    exact h)
  exact DriverTrace.stop7 b0 s1 b1 s2 b2 s3 b3 s4 b4 s5 b5 s6 b6 s7 b7 s8 stop7 hblock0 hblock1 hblock2 hblock3 hblock4 hblock5 hblock6 hblock7 hscan0 hscan1 hscan2 hscan3 hscan4 hscan5 hscan6 hscan7 hf.1 hf.2

#print axioms finishAdvance_success
#print axioms finish_success_iff
#print axioms successful_driver_has_trace
end AspisR1Query31Transcript
