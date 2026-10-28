import AspisR1TerminalDecoder.Funs
import R1Z.PV_RunJoin_RejectionProof28
import R1Z.PV_RunJoin_BranchDomain28
set_option autoImplicit false
namespace R1Z.PV_RunJoin_CodecSuccess29
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open R1Z.PV_RunJoin_ResultDomain28 R1Z.PV_RunJoin_ControlDomain28
open R1Z.PV_RunJoin_RejectionProof28

/-- Exact operational success path of snapshot decoding, retaining
all primitive calls, Try branches, and header/digest rejection precedence. -/
def Path (bytes : Slice U8) : Prop :=
  let i := Slice.len bytes
  if i != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  then False
  else
    ∃ s, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) bytes { «end» := 8#usize }) = ok s ∧
    ∃ s1, (core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC { start := 0#usize, «end» := 8#usize }) = ok s1 ∧
    ∃ b, (core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s s1) = ok b ∧
    if b
    then False
    else
      ∃ i1, (Slice.index_usize bytes 8#usize) = ok i1 ∧
      if i1 != pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION
      then False
      else
        ∃ i2, (Slice.index_usize bytes 9#usize) = ok i2 ∧
        if i2 != 0#u8
        then False
        else
          ∃ i3, (Slice.index_usize bytes 10#usize) = ok i3 ∧
          if i3 != 0#u8
          then False
          else
            ∃ i4, (Slice.index_usize bytes 11#usize) = ok i4 ∧
            if i4 != 0#u8
            then False
            else
              ∃ i5, (Slice.index_usize bytes 12#usize) = ok i5 ∧
              if i5 != 0#u8
              then False
              else
                ∃ i6, (Slice.index_usize bytes 13#usize) = ok i6 ∧
                if i6 != 0#u8
                then False
                else
                  ∃ i7, (Slice.index_usize bytes 14#usize) = ok i7 ∧
                  if i7 != 0#u8
                  then False
                  else
                    ∃ i8, (Slice.index_usize bytes 15#usize) = ok i8 ∧
                    if i8 != 0#u8
                    then False
                    else
                      ∃ s2, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 16#usize, «end» := 48#usize }) = ok s2 ∧
                      ∃ a, (pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_FORMAT_BINDING) = ok a ∧
                      ∃ s3, (core.array.Array.index (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) a { start := 0#usize, «end» := 32#usize }) = ok s3 ∧
                      ∃ b1, (core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8) s2 s3) = ok b1 ∧
                      if b1
                      then False
                      else
                        ∃ s4, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 128#usize, «end» := 160#usize }) = ok s4 ∧
                        ∃ r, (core.array.TryFromSharedArraySlice.try_from 32#usize s4) = ok r ∧
                        ∃ a1, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r) = ok a1 ∧
                        ∃ r1, (atomic_statement.decode_digest_canonical a1) = ok r1 ∧
                        ∃ r2, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r1 ()) = ok r2 ∧
                        ∃ cf, (core.result.Result.Insts.CoreOpsTry.branch r2) = ok cf ∧
                        match cf with
                        | core.ops.control_flow.ControlFlow.Continue val =>
                          ∃ s5, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 160#usize, «end» := 192#usize }) = ok s5 ∧
                          ∃ r3, (core.array.TryFromSharedArraySlice.try_from 32#usize s5) = ok r3 ∧
                          ∃ a2, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r3) = ok a2 ∧
                          ∃ r4, (atomic_statement.decode_digest_canonical a2) = ok r4 ∧
                          ∃ r5, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_1.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r4 ()) = ok r5 ∧
                          ∃ cf1, (core.result.Result.Insts.CoreOpsTry.branch r5) = ok cf1 ∧
                          match cf1 with
                          | core.ops.control_flow.ControlFlow.Continue val1 =>
                            ∃ s6, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 192#usize, «end» := 224#usize }) = ok s6 ∧
                            ∃ r6, (core.array.TryFromSharedArraySlice.try_from 32#usize s6) = ok r6 ∧
                            ∃ a3, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r6) = ok a3 ∧
                            ∃ r7, (atomic_statement.decode_digest_canonical a3) = ok r7 ∧
                            ∃ r8, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_2.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r7 ()) = ok r8 ∧
                            ∃ cf2, (core.result.Result.Insts.CoreOpsTry.branch r8) = ok cf2 ∧
                            match cf2 with
                            | core.ops.control_flow.ControlFlow.Continue val2 =>
                              ∃ s7, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 224#usize, «end» := 256#usize }) = ok s7 ∧
                              ∃ r9, (core.array.TryFromSharedArraySlice.try_from 32#usize s7) = ok r9 ∧
                              ∃ a4, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r9) = ok a4 ∧
                              ∃ r10, (atomic_statement.decode_digest_canonical a4) = ok r10 ∧
                              ∃ r11, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_3.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r10 ()) = ok r11 ∧
                              ∃ cf3, (core.result.Result.Insts.CoreOpsTry.branch r11) = ok cf3 ∧
                              match cf3 with
                              | core.ops.control_flow.ControlFlow.Continue val3 =>
                                ∃ s8, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 256#usize, «end» := 288#usize }) = ok s8 ∧
                                ∃ r12, (core.array.TryFromSharedArraySlice.try_from 32#usize s8) = ok r12 ∧
                                ∃ a5, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r12) = ok a5 ∧
                                ∃ r13, (atomic_statement.decode_digest_canonical a5) = ok r13 ∧
                                ∃ r14, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_4.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r13 ()) = ok r14 ∧
                                ∃ cf4, (core.result.Result.Insts.CoreOpsTry.branch r14) = ok cf4 ∧
                                match cf4 with
                                | core.ops.control_flow.ControlFlow.Continue val4 =>
                                  ∃ s9, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 288#usize, «end» := 320#usize }) = ok s9 ∧
                                  ∃ r15, (core.array.TryFromSharedArraySlice.try_from 32#usize s9) = ok r15 ∧
                                  ∃ a6, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r15) = ok a6 ∧
                                  ∃ r16, (atomic_statement.decode_digest_canonical a6) = ok r16 ∧
                                  ∃ r17, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_5.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r16 ()) = ok r17 ∧
                                  ∃ cf5, (core.result.Result.Insts.CoreOpsTry.branch r17) = ok cf5 ∧
                                  match cf5 with
                                  | core.ops.control_flow.ControlFlow.Continue val5 =>
                                    ∃ s10, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 320#usize, «end» := 352#usize }) = ok s10 ∧
                                    ∃ r18, (core.array.TryFromSharedArraySlice.try_from 32#usize s10) = ok r18 ∧
                                    ∃ a7, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r18) = ok a7 ∧
                                    ∃ r19, (atomic_statement.decode_digest_canonical a7) = ok r19 ∧
                                    ∃ r20, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_6.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r19 ()) = ok r20 ∧
                                    ∃ cf6, (core.result.Result.Insts.CoreOpsTry.branch r20) = ok cf6 ∧
                                    match cf6 with
                                    | core.ops.control_flow.ControlFlow.Continue val6 =>
                                      ∃ s11, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 352#usize, «end» := 384#usize }) = ok s11 ∧
                                      ∃ r21, (core.array.TryFromSharedArraySlice.try_from 32#usize s11) = ok r21 ∧
                                      ∃ a8, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r21) = ok a8 ∧
                                      ∃ r22, (atomic_statement.decode_digest_canonical a8) = ok r22 ∧
                                      ∃ r23, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_7.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r22 ()) = ok r23 ∧
                                      ∃ cf7, (core.result.Result.Insts.CoreOpsTry.branch r23) = ok cf7 ∧
                                      match cf7 with
                                      | core.ops.control_flow.ControlFlow.Continue val7 =>
                                        ∃ s12, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 384#usize, «end» := 416#usize }) = ok s12 ∧
                                        ∃ r24, (core.array.TryFromSharedArraySlice.try_from 32#usize s12) = ok r24 ∧
                                        ∃ a9, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r24) = ok a9 ∧
                                        ∃ r25, (atomic_statement.decode_digest_canonical a9) = ok r25 ∧
                                        ∃ r26, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_8.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r25 ()) = ok r26 ∧
                                        ∃ cf8, (core.result.Result.Insts.CoreOpsTry.branch r26) = ok cf8 ∧
                                        match cf8 with
                                        | core.ops.control_flow.ControlFlow.Continue val8 =>
                                          ∃ s13, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 416#usize, «end» := 448#usize }) = ok s13 ∧
                                          ∃ r27, (core.array.TryFromSharedArraySlice.try_from 32#usize s13) = ok r27 ∧
                                          ∃ a10, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r27) = ok a10 ∧
                                          ∃ r28, (atomic_statement.decode_digest_canonical a10) = ok r28 ∧
                                          ∃ r29, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_9.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r28 ()) = ok r29 ∧
                                          ∃ cf9, (core.result.Result.Insts.CoreOpsTry.branch r29) = ok cf9 ∧
                                          match cf9 with
                                          | core.ops.control_flow.ControlFlow.Continue val9 =>
                                            ∃ s14, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 448#usize, «end» := 480#usize }) = ok s14 ∧
                                            ∃ r30, (core.array.TryFromSharedArraySlice.try_from 32#usize s14) = ok r30 ∧
                                            ∃ a11, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r30) = ok a11 ∧
                                            ∃ r31, (atomic_statement.decode_digest_canonical a11) = ok r31 ∧
                                            ∃ r32, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_10.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r31 ()) = ok r32 ∧
                                            ∃ cf10, (core.result.Result.Insts.CoreOpsTry.branch r32) = ok cf10 ∧
                                            match cf10 with
                                            | core.ops.control_flow.ControlFlow.Continue val10 =>
                                              ∃ s15, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 480#usize, «end» := 512#usize }) = ok s15 ∧
                                              ∃ r33, (core.array.TryFromSharedArraySlice.try_from 32#usize s15) = ok r33 ∧
                                              ∃ a12, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r33) = ok a12 ∧
                                              ∃ r34, (atomic_statement.decode_digest_canonical a12) = ok r34 ∧
                                              ∃ r35, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_11.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r34 ()) = ok r35 ∧
                                              ∃ cf11, (core.result.Result.Insts.CoreOpsTry.branch r35) = ok cf11 ∧
                                              match cf11 with
                                              | core.ops.control_flow.ControlFlow.Continue val11 =>
                                                ∃ s16, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 512#usize, «end» := 544#usize }) = ok s16 ∧
                                                ∃ r36, (core.array.TryFromSharedArraySlice.try_from 32#usize s16) = ok r36 ∧
                                                ∃ a13, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r36) = ok a13 ∧
                                                ∃ r37, (atomic_statement.decode_digest_canonical a13) = ok r37 ∧
                                                ∃ r38, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_12.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r37 ()) = ok r38 ∧
                                                ∃ cf12, (core.result.Result.Insts.CoreOpsTry.branch r38) = ok cf12 ∧
                                                match cf12 with
                                                | core.ops.control_flow.ControlFlow.Continue val12 =>
                                                  ∃ s17, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 544#usize, «end» := 576#usize }) = ok s17 ∧
                                                  ∃ r39, (core.array.TryFromSharedArraySlice.try_from 32#usize s17) = ok r39 ∧
                                                  ∃ a14, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r39) = ok a14 ∧
                                                  ∃ r40, (atomic_statement.decode_digest_canonical a14) = ok r40 ∧
                                                  ∃ r41, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_13.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r40 ()) = ok r41 ∧
                                                  ∃ cf13, (core.result.Result.Insts.CoreOpsTry.branch r41) = ok cf13 ∧
                                                  match cf13 with
                                                  | core.ops.control_flow.ControlFlow.Continue val13 =>
                                                    ∃ s18, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 576#usize, «end» := 608#usize }) = ok s18 ∧
                                                    ∃ r42, (core.array.TryFromSharedArraySlice.try_from 32#usize s18) = ok r42 ∧
                                                    ∃ a15, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r42) = ok a15 ∧
                                                    ∃ r43, (atomic_statement.decode_digest_canonical a15) = ok r43 ∧
                                                    ∃ r44, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_14.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r43 ()) = ok r44 ∧
                                                    ∃ cf14, (core.result.Result.Insts.CoreOpsTry.branch r44) = ok cf14 ∧
                                                    match cf14 with
                                                    | core.ops.control_flow.ControlFlow.Continue val14 =>
                                                      ∃ s19, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 608#usize, «end» := 640#usize }) = ok s19 ∧
                                                      ∃ r45, (core.array.TryFromSharedArraySlice.try_from 32#usize s19) = ok r45 ∧
                                                      ∃ a16, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r45) = ok a16 ∧
                                                      ∃ r46, (atomic_statement.decode_digest_canonical a16) = ok r46 ∧
                                                      ∃ r47, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_15.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r46 ()) = ok r47 ∧
                                                      ∃ cf15, (core.result.Result.Insts.CoreOpsTry.branch r47) = ok cf15 ∧
                                                      match cf15 with
                                                      | core.ops.control_flow.ControlFlow.Continue val15 =>
                                                        ∃ s20, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 640#usize, «end» := 672#usize }) = ok s20 ∧
                                                        ∃ r48, (core.array.TryFromSharedArraySlice.try_from 32#usize s20) = ok r48 ∧
                                                        ∃ a17, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r48) = ok a17 ∧
                                                        ∃ r49, (atomic_statement.decode_digest_canonical a17) = ok r49 ∧
                                                        ∃ r50, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_16.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r49 ()) = ok r50 ∧
                                                        ∃ cf16, (core.result.Result.Insts.CoreOpsTry.branch r50) = ok cf16 ∧
                                                        match cf16 with
                                                        | core.ops.control_flow.ControlFlow.Continue val16 =>
                                                          ∃ s21, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 672#usize, «end» := 704#usize }) = ok s21 ∧
                                                          ∃ r51, (core.array.TryFromSharedArraySlice.try_from 32#usize s21) = ok r51 ∧
                                                          ∃ a18, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r51) = ok a18 ∧
                                                          ∃ r52, (atomic_statement.decode_digest_canonical a18) = ok r52 ∧
                                                          ∃ r53, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_17.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r52 ()) = ok r53 ∧
                                                          ∃ cf17, (core.result.Result.Insts.CoreOpsTry.branch r53) = ok cf17 ∧
                                                          match cf17 with
                                                          | core.ops.control_flow.ControlFlow.Continue val17 =>
                                                            ∃ s22, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 704#usize, «end» := 736#usize }) = ok s22 ∧
                                                            ∃ r54, (core.array.TryFromSharedArraySlice.try_from 32#usize s22) = ok r54 ∧
                                                            ∃ a19, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r54) = ok a19 ∧
                                                            ∃ r55, (atomic_statement.decode_digest_canonical a19) = ok r55 ∧
                                                            ∃ r56, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_18.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r55 ()) = ok r56 ∧
                                                            ∃ cf18, (core.result.Result.Insts.CoreOpsTry.branch r56) = ok cf18 ∧
                                                            match cf18 with
                                                            | core.ops.control_flow.ControlFlow.Continue val18 =>
                                                              ∃ s23, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 736#usize, «end» := 768#usize }) = ok s23 ∧
                                                              ∃ r57, (core.array.TryFromSharedArraySlice.try_from 32#usize s23) = ok r57 ∧
                                                              ∃ a20, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r57) = ok a20 ∧
                                                              ∃ r58, (atomic_statement.decode_digest_canonical a20) = ok r58 ∧
                                                              ∃ r59, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_19.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r58 ()) = ok r59 ∧
                                                              ∃ cf19, (core.result.Result.Insts.CoreOpsTry.branch r59) = ok cf19 ∧
                                                              match cf19 with
                                                              | core.ops.control_flow.ControlFlow.Continue val19 =>
                                                                ∃ s24, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 768#usize, «end» := 800#usize }) = ok s24 ∧
                                                                ∃ r60, (core.array.TryFromSharedArraySlice.try_from 32#usize s24) = ok r60 ∧
                                                                ∃ a21, (atomic_statement.unwrap_fixed_slice (Shared0T.Insts.CoreMarkerCopy (Array Std.U8 32#usize)) r60) = ok a21 ∧
                                                                ∃ r61, (atomic_statement.decode_digest_canonical a21) = ok r61 ∧
                                                                ∃ r62, (core.result.Result.map_err pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1.closure_20.Insts.CoreOpsFunctionFnOnceTupleAtomicStatementErrorPoolV1PairLiveSnapshotErrorV1 r61 ()) = ok r62 ∧
                                                                ∃ cf20, (core.result.Result.Insts.CoreOpsTry.branch r62) = ok cf20 ∧
                                                                match cf20 with
                                                                | core.ops.control_flow.ControlFlow.Continue val20 =>
                                                                  ∃ s25, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 48#usize, «end» := 80#usize }) = ok s25 ∧
                                                                  ∃ r63, (core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s25) = ok r63 ∧
                                                                  ∃ a22, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r63) = ok a22 ∧
                                                                  ∃ s26, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 80#usize, «end» := 112#usize }) = ok s26 ∧
                                                                  ∃ r64, (core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s26) = ok r64 ∧
                                                                  ∃ a23, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 32#usize core.marker.CopyU8) r64) = ok a23 ∧
                                                                  ∃ s27, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 112#usize, «end» := 120#usize }) = ok s27 ∧
                                                                  ∃ r65, (core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s27) = ok r65 ∧
                                                                  ∃ a24, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r65) = ok a24 ∧
                                                                  ∃ i9, (lift (core.num.U64.from_le_bytes a24)) = ok i9 ∧
                                                                  ∃ s28, (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) bytes { start := 120#usize, «end» := 128#usize }) = ok s28 ∧
                                                                  ∃ r66, (core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 s28) = ok r66 ∧
                                                                  ∃ a25, (atomic_statement.unwrap_fixed_slice (Array.Insts.CoreMarkerCopy 8#usize core.marker.CopyU8) r66) = ok a25 ∧
                                                                  ∃ i10, (lift (core.num.U64.from_le_bytes a25)) = ok i10 ∧
                                                                  ∃ r67, (pool_v1.pair_tree_profile.validate_pool_v1_pair_live_snapshot_v1 { pool := a22, deployment_domain := a23, sequence := i9, next_pair_index := i10, current_root := val, frontier := (Array.make 20#usize [ val1, val2, val3, val4, val5, val6, val7, val8, val9, val10, val11, val12, val13, val14, val15, val16, val17, val18, val19, val20 ]) }) = ok r67 ∧
                                                                  ∃ cf21, (core.result.Result.Insts.CoreOpsTry.branch r67) = ok cf21 ∧
                                                                  match cf21 with
                                                                  | core.ops.control_flow.ControlFlow.Continue _ => True
                                                                  | core.ops.control_flow.ControlFlow.Break residual => False
                                                                | core.ops.control_flow.ControlFlow.Break residual => False
                                                              | core.ops.control_flow.ControlFlow.Break residual => False
                                                            | core.ops.control_flow.ControlFlow.Break residual => False
                                                          | core.ops.control_flow.ControlFlow.Break residual => False
                                                        | core.ops.control_flow.ControlFlow.Break residual => False
                                                      | core.ops.control_flow.ControlFlow.Break residual => False
                                                    | core.ops.control_flow.ControlFlow.Break residual => False
                                                  | core.ops.control_flow.ControlFlow.Break residual => False
                                                | core.ops.control_flow.ControlFlow.Break residual => False
                                              | core.ops.control_flow.ControlFlow.Break residual => False
                                            | core.ops.control_flow.ControlFlow.Break residual => False
                                          | core.ops.control_flow.ControlFlow.Break residual => False
                                        | core.ops.control_flow.ControlFlow.Break residual => False
                                      | core.ops.control_flow.ControlFlow.Break residual => False
                                    | core.ops.control_flow.ControlFlow.Break residual => False
                                  | core.ops.control_flow.ControlFlow.Break residual => False
                                | core.ops.control_flow.ControlFlow.Break residual => False
                              | core.ops.control_flow.ControlFlow.Break residual => False
                            | core.ops.control_flow.ControlFlow.Break residual => False
                          | core.ops.control_flow.ControlFlow.Break residual => False
                        | core.ops.control_flow.ControlFlow.Break residual => False

theorem iff_path (bytes : Slice U8) :
    (∃ snapshot, pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 bytes = ok (.Ok snapshot)) ↔ Path bytes := by
  rw [success_wp]
  unfold pool_v1.pair_tree_profile.decode_pool_v1_pair_live_snapshot_v1 Path
  simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp]
  repeat' first
    | rfl
    | (apply exists_congr; intro value)
    | (apply and_congr_right; intro hprefix)
    | (apply R1Z.PV_RunJoin_BranchDomain28.ite_iff <;> intro hcond)
    | (cases value <;> simp only [bind_wp,ite_wp,ok_wp,isRustOk_ok,isRustOk_err,residual_wp])
#print axioms iff_path
end R1Z.PV_RunJoin_CodecSuccess29
