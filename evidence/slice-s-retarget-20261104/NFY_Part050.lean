import Lean
import NFY_Part049
import NFY_Part048
import NFS_AccumPart01
import NFY_Part043
import NBP_Read
import NFY_Part042

-- BEGIN copied NFD_EmitProjection: evidence/slice-s-compose10-20261104/NFD_EmitProjection.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_EmitProjection
open Aeneas Aeneas.Std
open NFY_NEU_EmitModel
open NFY_NEU_PublicProjections (get)
def kindCode : AspisR1TerminalDecoder.pool_v1.historical_anchor.PoolV1TransitionKind → Nat
  | .PrivateTransfer => 1 | .Withdrawal => 2

def project (r : Output) (slot : Fin 8) (i : Fin 8) (j : Fin 32) (k : Fin 20) : Nat :=
  match slot.val with
  | 0 => kindCode r.transition_kind
  | 1 => (get r.master_account j).val
  | 2 => (get r.selected_lane_account j).val
  | 3 => r.output_lane.val
  | 4 => (get r.nullifier i).val
  | 5 => r.verified_afterstate.next_pair_index.val
  | 6 => (get r.verified_afterstate.next_root i).val
  | _ => (get (get r.verified_afterstate.next_frontier k) i).val

theorem complete (a b : Output)
    (point : ∀ slot i j k, project a slot i j k=project b slot i j k) : a=b := by
  have h0 : a.transition_kind=b.transition_kind := by
    have h := point ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
    cases ha : a.transition_kind <;> cases hb : b.transition_kind <;>
      simp_all [project,kindCode]
  have h1 : a.master_account=b.master_account := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨1,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h2 : a.selected_lane_account=b.selected_lane_account := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨2,by decide⟩ ⟨0,by decide⟩ j ⟨0,by decide⟩
  have h3 : a.output_lane=b.output_lane := by
    apply UScalar.eq_of_val_eq
    exact point ⟨3,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h4 : a.nullifier=b.nullifier := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨4,by decide⟩ i ⟨0,by decide⟩ ⟨0,by decide⟩
  have h5 : a.verified_afterstate.next_pair_index=b.verified_afterstate.next_pair_index := by
    apply UScalar.eq_of_val_eq
    exact point ⟨5,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
  have h6 : a.verified_afterstate.next_root=b.verified_afterstate.next_root := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨6,by decide⟩ i ⟨0,by decide⟩ ⟨0,by decide⟩
  have h7 : a.verified_afterstate.next_frontier=b.verified_afterstate.next_frontier := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro k
    apply NFY_NED_WindowExtensionality.array_ext
    intro i
    apply UScalar.eq_of_val_eq
    exact point ⟨7,by decide⟩ i ⟨0,by decide⟩ k
  cases a with
  | mk ak am asl al an aa =>
    cases aa
    cases b with
    | mk bk bm bsl bl bn ba =>
      cases ba
      simp_all only

theorem alignment0 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨0,by decide⟩ i j k = kindCode (AspisR1.S2K.ResultAdmission.kind s) := rfl
theorem alignment1 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨1,by decide⟩ i j k = (get (AspisR1.S2K.StatementAdmission.common s).master_account j).val := rfl
theorem alignment2 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨2,by decide⟩ i j k = (get (AspisR1.S2K.StatementAdmission.common s).selected_lane_account j).val := rfl
theorem alignment3 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨3,by decide⟩ i j k = (AspisR1.S2K.StatementAdmission.common s).output_lane.val := rfl
theorem alignment4 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨4,by decide⟩ i j k = (get (AspisR1.S2K.StatementChecks.nullifier s) i).val := rfl
theorem alignment5 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨5,by decide⟩ i j k = (AspisR1.S2K.StatementAdmission.common s).lane_transition.candidate_afterstate.next_pair_index.val := rfl
theorem alignment6 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨6,by decide⟩ i j k = (get (AspisR1.S2K.StatementAdmission.common s).lane_transition.candidate_afterstate.next_root i).val := rfl
theorem alignment7 (s : Statement) (i : Fin 8) (j : Fin 32) (k : Fin 20) :
    project (derived s) ⟨7,by decide⟩ i j k = (get (get (AspisR1.S2K.StatementAdmission.common s).lane_transition.candidate_afterstate.next_frontier k) i).val := rfl

#print axioms complete
#print axioms alignment0
#print axioms alignment1
#print axioms alignment2
#print axioms alignment3
#print axioms alignment4
#print axioms alignment5
#print axioms alignment6
#print axioms alignment7
end NFY_NFD_EmitProjection
-- END copied NFD_EmitProjection
-- BEGIN copied NFD_RawCarriers: evidence/slice-s-compose10-20261104/NFD_RawCarriers.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RawCarriers
open Aeneas Aeneas.Std
abbrev Wide := FIo_Native.aspis_core.field.wide_exact.WideExact

def make (a b c d e f g h : U32) : Wide :=
  ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
theorem raw_roundtrip (x : Wide) :
    make x.c0.c0.a x.c0.c0.b x.c0.c1.a x.c0.c1.b
      x.c1.c0.a x.c1.c0.b x.c1.c1.a x.c1.c1.b = x := rfl

theorem limbs_result_state_effects {State : Type} (x : Wide) (state : State) :
    (FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs x,state,([] : List Unit)) =
    (Result.ok (Array.make 8#usize [x.c0.c0.a,x.c0.c0.b,x.c0.c1.a,x.c0.c1.b,
      x.c1.c0.a,x.c1.c0.b,x.c1.c1.a,x.c1.c1.b]),state,[]) := by
  rw [NFS_NBG_WideCarriers.to_limbs_result]

def fromPort : NFY_NBG_Transport.CV → NFY_NBG_Transport.V
  | .S1 => .S1 | .S2 => .S2 | .D => .D
theorem tag_roundtrip (v : NFY_NBG_Transport.V) : fromPort (NFY_NBG_Transport.port v)=v := by
  cases v <;> rfl

theorem tag_result_state_effects {State : Type} (v : NFY_NBG_Transport.V) (state : State) :
    (AspisR1PublicPreparation.transport.Variant.tag v,state,([] : List Unit)) =
    (AspisR1.CheckpointBytes4Ops.tag (NFY_NBG_Transport.port v),state,[]) := by
  rw [NFY_NBG_Transport.tag_result]

#print axioms raw_roundtrip
#print axioms limbs_result_state_effects
#print axioms tag_roundtrip
#print axioms tag_result_state_effects
end NFY_NFD_RawCarriers
-- END copied NFD_RawCarriers
-- BEGIN copied NED_ReadDomains: evidence/slice-s-compose-20261029/NED_ReadDomains.lean
set_option autoImplicit false
namespace NFY_NED_ReadDomains
open Aeneas Aeneas.Std Result

/-- The reached slice conversion is Ok on the SAME selected bytes; the
callee's unwrap domain is proved, not inferred from a successful parent. -/
theorem converted {N W : Usize} (bytes : Array U8 N) (start stop : Usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ N.val)
    (width : stop.val-start.val = W.val) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start,«end»:=stop}
        core.array.TryFromArrayCopySlice.try_from W core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk bytes start.val (by omega))) := by
  have room : W.val ≤ N.val-start.val := by omega
  simp [room,core.array.Array.index,core.ops.index.IndexSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index,Array.to_slice,
    Slice.length,Slice.len,order,bound,bytes.property,
    core.array.TryFromArrayCopySlice.try_from,List.slice,List.length_take,
    List.length_drop,width,NBP_Read.chunk]

theorem bytes_retained {N W : Usize} (bytes : Array U8 N) (start : Nat)
    (bound : start+W.val ≤ N.val) :
    (NBP_Read.chunk (W:=W) bytes start bound).val = (bytes.val.drop start).take W.val := rfl

#print axioms converted
#print axioms bytes_retained
end NFY_NED_ReadDomains
-- END copied NED_ReadDomains
-- BEGIN copied NED_RequestReadWindows: evidence/slice-s-compose-20261029/NED_RequestReadWindows.lean
set_option autoImplicit false
namespace NFY_NED_RequestReadWindows
open Aeneas Aeneas.Std Result
theorem profile (bytes : Array U8 320#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=8#usize,«end»:=40#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 8 (by decide))) :=
  NFY_NED_ReadDomains.converted bytes 8#usize 40#usize (by decide) (by decide) (by decide)
#print axioms profile
theorem release (bytes : Array U8 320#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=40#usize,«end»:=72#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 40 (by decide))) :=
  NFY_NED_ReadDomains.converted bytes 40#usize 72#usize (by decide) (by decide) (by decide)
#print axioms release
theorem pool_program (bytes : Array U8 320#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=72#usize,«end»:=104#usize}
        core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=32#usize) bytes 72 (by decide))) :=
  NFY_NED_ReadDomains.converted bytes 72#usize 104#usize (by decide) (by decide) (by decide)
#print axioms pool_program
theorem payment (bytes : Array U8 320#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=104#usize,«end»:=320#usize}
        core.array.TryFromArrayCopySlice.try_from 216#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=216#usize) bytes 104 (by decide))) :=
  NFY_NED_ReadDomains.converted bytes 104#usize 320#usize (by decide) (by decide) (by decide)
#print axioms payment
end NFY_NED_RequestReadWindows
-- END copied NED_RequestReadWindows
-- BEGIN copied NFD_RequestOracle: evidence/slice-s-compose10-20261104/NFD_RequestOracle.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestOracle
open Aeneas Aeneas.Std Result AspisR20Request
def run
  (transfer : Slice U8 → Result (core.result.Result pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 pool_v1.payment_relation.PoolV1PaymentStatementFormatError))
  (withdrawal : Slice U8 → Result (core.result.Result pool_v1.payment_relation.PoolV1WithdrawalPublicV1 pool_v1.payment_relation.PoolV1PaymentStatementFormatError))
  (bytes : Array Std.U8 320#usize) :
  Result (core.result.Result
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
  := do
  let s ← lift (Array.to_slice bytes)
  let i := Slice.len s
  let i1 ←
    pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES
  if i != i1
  then
    ok (core.result.Result.Err
      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength)
  else
    let s1 ←
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8)) bytes
        { «end» := 4#usize }
    let b ←
      Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8 s1
        pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC
    if b
    then
      ok (core.result.Result.Err
        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongMagic)
    else
      let i2 ← Array.index_usize bytes 4#usize
      if i2 !=
        pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_VERSION
      then
        ok (core.result.Result.Err
          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongVersion)
      else
        let i3 ← Array.index_usize bytes 5#usize
        let r ← pool_v1.pair_forest_terminal.transition_kind i3
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val =>
          let i4 ← Array.index_usize bytes 6#usize
          if i4 != pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION
          then
            ok (core.result.Result.Err
              pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongDigestEncoding)
          else
            let i5 ← Array.index_usize bytes 7#usize
            if i5 != 0#u8
            then
              ok (core.result.Result.Err
                pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
            else
              match val with
              | pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer
                =>
                let s2 ←
                  core.array.Array.index (core.ops.index.IndexSlice
                    (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8))
                    bytes
                    {
                      start :=
                        pool_v1.pair_forest_terminal.REQUEST_PAYMENT_OFFSET
                    }
                let r1 ←
                  transfer
                    s2
                let r2 ←
                  core.result.Result.map_err
                    pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
                    r1 ()
                let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val1 =>
                  let s3 ←
                    core.array.Array.index (core.ops.index.IndexSlice
                      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                      bytes
                      {
                        start :=
                          pool_v1.pair_forest_terminal.REQUEST_PROFILE_OFFSET,
                        «end» :=
                          pool_v1.pair_forest_terminal.REQUEST_RELEASE_OFFSET
                      }
                  let r3 ←
                    core.array.TryFromArrayCopySlice.try_from 32#usize
                      core.marker.CopyU8 s3
                  let r4 ←
                    core.result.Result.map_err
                      pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                      r3 ()
                  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
                  match cf2 with
                  | core.ops.control_flow.ControlFlow.Continue val2 =>
                    let s4 ←
                      core.array.Array.index (core.ops.index.IndexSlice
                        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                        bytes
                        {
                          start :=
                            pool_v1.pair_forest_terminal.REQUEST_RELEASE_OFFSET,
                          «end» :=
                            pool_v1.pair_forest_terminal.REQUEST_POOL_PROGRAM_OFFSET
                        }
                    let r5 ←
                      core.array.TryFromArrayCopySlice.try_from 32#usize
                        core.marker.CopyU8 s4
                    let r6 ←
                      core.result.Result.map_err
                        pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                        r5 ()
                    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf3 with
                    | core.ops.control_flow.ControlFlow.Continue val3 =>
                      let s5 ←
                        core.array.Array.index (core.ops.index.IndexSlice
                          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                          bytes
                          {
                            start :=
                              pool_v1.pair_forest_terminal.REQUEST_POOL_PROGRAM_OFFSET,
                            «end» :=
                              pool_v1.pair_forest_terminal.REQUEST_PAYMENT_OFFSET
                          }
                      let r7 ←
                        core.array.TryFromArrayCopySlice.try_from 32#usize
                          core.marker.CopyU8 s5
                      let r8 ←
                        core.result.Result.map_err
                          pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                          r7 ()
                      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r8
                      match cf4 with
                      | core.ops.control_flow.ControlFlow.Continue val4 =>
                        let a := Array.repeat 32#usize 0#u8
                        let b1 ←
                          core.array.equality.PartialEqArray.eq
                            core.cmp.PartialEqU8 val2 a
                        if b1
                        then
                          ok (core.result.Result.Err
                            pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                        else
                          let a1 := Array.repeat 32#usize 0#u8
                          let b2 ←
                            core.array.equality.PartialEqArray.eq
                              core.cmp.PartialEqU8 val3 a1
                          if b2
                          then
                            ok (core.result.Result.Err
                              pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                          else
                            let a2 := Array.repeat 32#usize 0#u8
                            let b3 ←
                              core.array.equality.PartialEqArray.eq
                                core.cmp.PartialEqU8 val4 a2
                            if b3
                            then
                              ok (core.result.Result.Err
                                pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                            else
                              ok (core.result.Result.Ok
                                {
                                  verifier_profile := val2,
                                  verifier_release := val3,
                                  pool_program := val4,
                                  «public» :=
                                    (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1.PrivateTransfer
                                      val1)
                                })
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                          (core.convert.FromSame
                          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                          residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                        (core.convert.FromSame
                        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                        residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                      (core.convert.FromSame
                      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                    (core.convert.FromSame
                    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                    residual
              | pool_v1.historical_anchor.PoolV1TransitionKind.Withdrawal =>
                let s2 ←
                  core.array.Array.index (core.ops.index.IndexSlice
                    (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8))
                    bytes
                    {
                      start :=
                        pool_v1.pair_forest_terminal.REQUEST_PAYMENT_OFFSET
                    }
                let r1 ←
                  withdrawal
                    s2
                let r2 ←
                  core.result.Result.map_err
                    pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PaymentStatementFormatErrorPoolV1PairForestTerminalFormatErrorV1
                    r1 ()
                let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r2
                match cf1 with
                | core.ops.control_flow.ControlFlow.Continue val1 =>
                  let s3 ←
                    core.array.Array.index (core.ops.index.IndexSlice
                      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                      bytes
                      {
                        start :=
                          pool_v1.pair_forest_terminal.REQUEST_PROFILE_OFFSET,
                        «end» :=
                          pool_v1.pair_forest_terminal.REQUEST_RELEASE_OFFSET
                      }
                  let r3 ←
                    core.array.TryFromArrayCopySlice.try_from 32#usize
                      core.marker.CopyU8 s3
                  let r4 ←
                    core.result.Result.map_err
                      pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                      r3 ()
                  let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r4
                  match cf2 with
                  | core.ops.control_flow.ControlFlow.Continue val2 =>
                    let s4 ←
                      core.array.Array.index (core.ops.index.IndexSlice
                        (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                        bytes
                        {
                          start :=
                            pool_v1.pair_forest_terminal.REQUEST_RELEASE_OFFSET,
                          «end» :=
                            pool_v1.pair_forest_terminal.REQUEST_POOL_PROGRAM_OFFSET
                        }
                    let r5 ←
                      core.array.TryFromArrayCopySlice.try_from 32#usize
                        core.marker.CopyU8 s4
                    let r6 ←
                      core.result.Result.map_err
                        pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                        r5 ()
                    let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r6
                    match cf3 with
                    | core.ops.control_flow.ControlFlow.Continue val3 =>
                      let s5 ←
                        core.array.Array.index (core.ops.index.IndexSlice
                          (core.slice.index.SliceIndexRangeUsizeSlice Std.U8))
                          bytes
                          {
                            start :=
                              pool_v1.pair_forest_terminal.REQUEST_POOL_PROGRAM_OFFSET,
                            «end» :=
                              pool_v1.pair_forest_terminal.REQUEST_PAYMENT_OFFSET
                          }
                      let r7 ←
                        core.array.TryFromArrayCopySlice.try_from 32#usize
                          core.marker.CopyU8 s5
                      let r8 ←
                        core.result.Result.map_err
                          pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleTryFromSliceErrorPoolV1PairForestTerminalFormatErrorV1
                          r7 ()
                      let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r8
                      match cf4 with
                      | core.ops.control_flow.ControlFlow.Continue val4 =>
                        let a := Array.repeat 32#usize 0#u8
                        let b1 ←
                          core.array.equality.PartialEqArray.eq
                            core.cmp.PartialEqU8 val2 a
                        if b1
                        then
                          ok (core.result.Result.Err
                            pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                        else
                          let a1 := Array.repeat 32#usize 0#u8
                          let b2 ←
                            core.array.equality.PartialEqArray.eq
                              core.cmp.PartialEqU8 val3 a1
                          if b2
                          then
                            ok (core.result.Result.Err
                              pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                          else
                            let a2 := Array.repeat 32#usize 0#u8
                            let b3 ←
                              core.array.equality.PartialEqArray.eq
                                core.cmp.PartialEqU8 val4 a2
                            if b3
                            then
                              ok (core.result.Result.Err
                                pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.NonZeroBinding)
                            else
                              ok (core.result.Result.Ok
                                {
                                  verifier_profile := val2,
                                  verifier_release := val3,
                                  pool_program := val4,
                                  «public» :=
                                    (pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1.Withdrawal
                                      val1)
                                })
                      | core.ops.control_flow.ControlFlow.Break residual =>
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                          (core.convert.FromSame
                          pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                          residual
                    | core.ops.control_flow.ControlFlow.Break residual =>
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                        (core.convert.FromSame
                        pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                        residual
                  | core.ops.control_flow.ControlFlow.Break residual =>
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                      (core.convert.FromSame
                      pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                      residual
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
                    (core.convert.FromSame
                    pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
                    residual
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
            (core.convert.FromSame
            pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1)
            residual

/-- MODEL continuation part of ruling(y). The native certificate must separately
establish the exact same320-byte input and216-byte payment window. -/
theorem array_result_state_effects {State : Type} (bytes : Array U8 320#usize) (state : State) :
    (run pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 bytes,state,([] : List Unit)) =
    (pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1 bytes,state,[]) := by rfl

/-- The installed wrapper keeps every error constructor and the same parsed
request; no accepted fixture is assumed. -/
def runSlice (bytes : Slice U8) : Result (core.result.Result AspisR1.NFY_JHd_RequestNative.Request AspisR1.NFY_JHd_RequestNative.FormatError) := do
  let array ← core.array.TryFromSharedArraySlice.try_from 320#usize bytes
  match array with
  | .Err _ => ok (.Err AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength)
  | .Ok array =>
    let result ← run pool_v1.payment_relation.decode_pool_v1_private_transfer_public_v1
      pool_v1.payment_relation.decode_pool_v1_withdrawal_public_v1 array
    match result with
    | .Err error => ok (.Err (AspisR1.NFY_JHd_RequestCarrier.mapPoolV1PairForestTerminalFormatErrorV1 error))
    | .Ok request => ok (.Ok (AspisR1.NFY_JHd_RequestCarrier.request request))

theorem result_state_effects {State : Type} (bytes : Slice U8) (state : State) :
    (runSlice bytes,state,([] : List Unit)) =
    (AspisR1.NFY_JHd_RequestNative.decode bytes,state,[]) := by rfl

#print axioms array_result_state_effects
#print axioms result_state_effects
end NFY_NFD_RequestOracle
-- END copied NFD_RequestOracle
-- BEGIN copied NFD_RequestDomains: evidence/slice-s-compose10-20261104/NFD_RequestDomains.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestDomains
open Aeneas Aeneas.Std Result
abbrev Request := AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1

theorem payment_length (bytes : Array U8 320#usize) :
    (bytes.val.drop 104).length = 216 := by
  rw [List.length_drop,bytes.property]
  rfl

theorem binding_fields (p : Request) :
    (AspisR1.NFY_JHd_RequestCarrier.request p).verifier_profile = p.verifier_profile ∧
    (AspisR1.NFY_JHd_RequestCarrier.request p).verifier_release = p.verifier_release ∧
    (AspisR1.NFY_JHd_RequestCarrier.request p).pool_program = p.pool_program ∧
    (AspisR1.NFY_JHd_RequestCarrier.request p).«public» =
      AspisR1.NFY_JHd_RequestCarrier.payment p.«public» := ⟨rfl,rfl,rfl,rfl⟩

/-- No canonical restriction is added at the parser boundary: a payment decoder
receives exactly the216-byte suffix and establishes its own validation. -/
theorem payment_window (bytes : Array U8 320#usize) :
    (do let s ← core.array.Array.index
          (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
          bytes {start:=104#usize,«end»:=320#usize}
        core.array.TryFromArrayCopySlice.try_from 216#usize core.marker.CopyU8 s) =
    ok (.Ok (NBP_Read.chunk (W:=216#usize) bytes 104 (by decide))) :=
  NFY_NED_RequestReadWindows.payment bytes

theorem wrong_length (bytes : Slice U8) (bad : bytes.val.length ≠ 320) :
    NFY_NFD_RequestOracle.runSlice bytes = ok (.Err AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1.WrongLength) := by
  simp [NFY_NFD_RequestOracle.runSlice,core.array.TryFromSharedArraySlice.try_from,Slice.len,Slice.length,bad]

#print axioms wrong_length
#print axioms payment_length
#print axioms binding_fields
#print axioms payment_window
end NFY_NFD_RequestDomains
-- END copied NFD_RequestDomains
-- BEGIN copied NFD_RequestProjection: evidence/slice-s-compose10-20261104/NFD_RequestProjection.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestProjection
open Aeneas Aeneas.Std
open NFY_NEU_PublicProjections (get)
abbrev Request := NFY_NFD_RequestDomains.Request
abbrev T := AspisR20Request.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1
abbrev W := AspisR20Request.pool_v1.payment_relation.PoolV1WithdrawalPublicV1

def toT (p : T) : NFY_NEU_PublicProjections.Transfer :=
  AspisR1.JHf_Carrier.toPoolV1PrivateTransferPublicV1 (AspisR1.NFY_JHd_RequestCarrier.privateTransfer p)
def toW (p : W) : NFY_NEU_PublicProjections.Withdrawal :=
  AspisR1.JHf_Carrier.toPoolV1WithdrawalPublicV1 (AspisR1.NFY_JHd_RequestCarrier.withdrawal p)
def fromT (p : NFY_NEU_PublicProjections.Transfer) : T :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.recipient_commitment,p.change_commitment⟩
def fromW (p : NFY_NEU_PublicProjections.Withdrawal) : W :=
  ⟨p.pool,p.deployment_domain,p.anchor_sequence,p.anchor_root,p.nullifier,p.asset_id,p.amount,p.destination_token_account,p.change_commitment⟩
theorem transfer_roundtrip (p : T) : fromT (toT p)=p := rfl
theorem withdrawal_roundtrip (p : W) : fromW (toW p)=p := rfl

def project (s : Request) (slot : Fin 14) (i : Fin 8) (j : Fin 32) : Nat :=
  if h0 : slot.val=0 then (get s.verifier_profile j).val else
  if h1 : slot.val=1 then (get s.verifier_release j).val else
  if h2 : slot.val=2 then (get s.pool_program j).val else
  match s.«public» with
  | .PrivateTransfer p =>
    if h3 : slot.val=3 then 1 else
    if h : slot.val<12 then NFY_NEU_PublicProjections.transfer (toT p) ⟨slot.val-4,by omega⟩ i j else 0
  | .Withdrawal p =>
    if h3 : slot.val=3 then 2 else
    if h : slot.val<11 then NFY_NEU_PublicProjections.withdrawal (toW p) ⟨slot.val-4,by omega⟩ i j else
    if slot.val=12 then NFY_NEU_PublicProjections.withdrawal (toW p) ⟨7,by decide⟩ i j else
    if slot.val=13 then NFY_NEU_PublicProjections.withdrawal (toW p) ⟨8,by decide⟩ i j else 0

theorem complete (a b : Request)
    (point : ∀ slot i j, project a slot i j=project b slot i j) : a=b := by
  have hp : a.verifier_profile=b.verifier_profile := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨0,by decide⟩ ⟨0,by decide⟩ j
  have hr : a.verifier_release=b.verifier_release := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨1,by decide⟩ ⟨0,by decide⟩ j
  have hb : a.pool_program=b.pool_program := by
    apply NFY_NED_WindowExtensionality.array_ext
    intro j
    apply UScalar.eq_of_val_eq
    exact point ⟨2,by decide⟩ ⟨0,by decide⟩ j
  have pub : a.«public»=b.«public» := by
    cases ha : a.«public» with
    | PrivateTransfer p =>
      cases hq : b.«public» with
      | PrivateTransfer q =>
        have raw : toT p=toT q := by
          apply NFY_NEU_PublicProjections.transfer_ext
          intro slot i j
          have h := point ⟨slot.val+4,by omega⟩ i j
          simpa [project,ha,hq,show slot.val+4≠0 by omega,show slot.val+4≠1 by omega,
            show slot.val+4≠2 by omega,show slot.val+4≠3 by omega,show slot.val+4<12 by omega] using h
        have same := congrArg fromT raw
        simpa only [transfer_roundtrip] using congrArg AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1.PrivateTransfer same
      | Withdrawal q =>
        have h := point ⟨3,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
        simp [project,ha,hq] at h
    | Withdrawal p =>
      cases hq : b.«public» with
      | PrivateTransfer q =>
        have h := point ⟨3,by decide⟩ ⟨0,by decide⟩ ⟨0,by decide⟩
        simp [project,ha,hq] at h
      | Withdrawal q =>
        have raw : toW p=toW q := by
          apply NFY_NEU_PublicProjections.withdrawal_ext
          intro slot i j
          by_cases small : slot.val<7
          · have h := point ⟨slot.val+4,by omega⟩ i j
            simpa [project,ha,hq,show slot.val+4≠0 by omega,show slot.val+4≠1 by omega,
              show slot.val+4≠2 by omega,show slot.val+4≠3 by omega,show slot.val+4<11 by omega] using h
          · by_cases seven : slot.val=7
            · have eq : slot=⟨7,by decide⟩ := Fin.ext seven
              subst slot
              simpa [project,ha,hq] using point ⟨12,by decide⟩ i j
            · have eq : slot=⟨8,by decide⟩ := Fin.ext (by change slot.val=8;omega)
              subst slot
              simpa [project,ha,hq] using point ⟨13,by decide⟩ i j
        have same := congrArg fromW raw
        simpa only [withdrawal_roundtrip] using congrArg AspisR20Request.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1.Withdrawal same
  cases a;cases b
  congr 1 <;> assumption

#print axioms transfer_roundtrip
#print axioms withdrawal_roundtrip
#print axioms complete
end NFY_NFD_RequestProjection
-- END copied NFD_RequestProjection
-- BEGIN copied NFD_RequestField00: evidence/slice-s-compose10-20261104/NFD_RequestField00.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField00
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 (get s.verifier_profile j).val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨0,by decide⟩ i j=expected s i j := by
  rfl

#print axioms alignment
end NFY_NFD_RequestField00
-- END copied NFD_RequestField00
-- BEGIN copied NFD_RequestField01: evidence/slice-s-compose10-20261104/NFD_RequestField01.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField01
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 (get s.verifier_release j).val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨1,by decide⟩ i j=expected s i j := by
  rfl

#print axioms alignment
end NFY_NFD_RequestField01
-- END copied NFD_RequestField01
-- BEGIN copied NFD_RequestField02: evidence/slice-s-compose10-20261104/NFD_RequestField02.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NFD_RequestField02
open Aeneas Aeneas.Std NFY_NFD_RequestProjection
open NFY_NEU_PublicProjections (get)
def expected (s : Request) (i : Fin 8) (j : Fin 32) : Nat :=
 (get s.pool_program j).val
theorem alignment (s : Request) (i : Fin 8) (j : Fin 32) :
    project s ⟨2,by decide⟩ i j=expected s i j := by
  rfl

#print axioms alignment
end NFY_NFD_RequestField02
-- END copied NFD_RequestField02

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
