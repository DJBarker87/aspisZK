import Lean
import NFY_Part048
import NFY_Part040
import NFY_Part043
import AdapterRwScalar
import AdapterRwModel
import AspisR1AdapterReconstruct.Funs
import NFY_Part033
import Aeneas

-- BEGIN copied JHd_RequestWindow: lean/JHd_RequestWindow.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestWindow
open Aeneas Aeneas.Std Result WP

def value : Array U8 320#usize := ⟨NFY_JHb_DataRequest.bytes,NFY_JHb_DataRequest.length⟩
def window (off n : Nat) (bound : off+n≤320) : Slice U8 :=
  ⟨(NFY_JHb_DataRequest.bytes.drop off).take n,by
    have h : ((NFY_JHb_DataRequest.bytes.drop off).take n).length≤320 := by
      rw [List.length_take,List.length_drop,NFY_JHb_DataRequest.length]
      omega
    scalar_tac⟩

theorem length (off n : Nat) (bound : off+n≤320) :
    (window off n bound).val.length=n := by
  simp only [window,List.length_take,List.length_drop,NFY_JHb_DataRequest.length]
  omega
#print axioms length

theorem range (start stop : Usize) (order : start.val≤stop.val) (inside : stop.val≤320) :
    core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      value {start:=start,«end»:=stop}=
      ok (window start.val (stop.val-start.val) (by omega)) := by
  have size : value.val.length=320 := NFY_JHb_DataRequest.length
  have spec : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
      value {start:=start,«end»:=stop}
      ⦃ out => out=window start.val (stop.val-start.val) (by omega) ⦄ := by
    unfold core.array.Array.index core.ops.index.IndexSlice core.slice.index.Slice.index
    step*
    all_goals try (change stop.val ≤ value.val.length; omega)
    all_goals apply Subtype.ext
    all_goals simpa only [List.slice,window,value,Array.to_slice] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call
#print axioms range
end AspisR1.NFY_JHd_RequestWindow
-- END copied JHd_RequestWindow
-- BEGIN copied JHd_RequestBindings: lean/JHd_RequestBindings.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestBindings
open Aeneas Aeneas.Std Result NFY_JHd_RequestWindow

theorem profile : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    value {start:=8#usize,«end»:=40#usize}=ok (window 8 32 (by decide)) :=
  range 8#usize 40#usize (by decide) (by decide)
theorem release : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    value {start:=40#usize,«end»:=72#usize}=ok (window 40 32 (by decide)) :=
  range 40#usize 72#usize (by decide) (by decide)
theorem pool : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    value {start:=72#usize,«end»:=104#usize}=ok (window 72 32 (by decide)) :=
  range 72#usize 104#usize (by decide) (by decide)
#print axioms profile
#print axioms release
#print axioms pool

theorem profile_cast : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (window 8 32 (by decide))=ok (.Ok NFY_JHd_RequestValue.value.verifier_profile) := by
  apply NFY_JFt_ExactArray.cast
  exact NFY_JHb_RequestBindings.profile
#print axioms profile_cast

theorem release_cast : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (window 40 32 (by decide))=ok (.Ok NFY_JHd_RequestValue.value.verifier_release) := by
  apply NFY_JFt_ExactArray.cast
  exact NFY_JHb_RequestBindings.release
#print axioms release_cast

theorem pool_cast : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
    (window 72 32 (by decide))=ok (.Ok NFY_JHd_RequestValue.value.pool_program) := by
  apply NFY_JFt_ExactArray.cast
  exact NFY_JHb_RequestBindings.pool
#print axioms pool_cast
end AspisR1.NFY_JHd_RequestBindings
-- END copied JHd_RequestBindings
-- BEGIN copied JHd_RequestHead: lean/JHd_RequestHead.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestHead
open Aeneas Aeneas.Std Result WP NFY_JHd_RequestWindow

def magic : Slice U8 := ⟨[65#u8,83#u8,81#u8,56#u8],by simp;scalar_tac⟩

attribute [local irreducible] value magic

theorem first : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
    value {«end»:=4#usize}=ok magic := by
  have selected : NFY_JHb_DataRequest.bytes.take 4=magic.val := by unfold magic;rfl
  have size : value.to_slice.val.length=320 := by
    simp only [value,Array.to_slice]
    exact NFY_JHb_DataRequest.length
  have spec : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeToUsizeSlice U8))
      value {«end»:=4#usize} ⦃ out => out=magic ⦄ := by
    unfold core.array.Array.index core.ops.index.IndexSlice core.slice.index.Slice.index
    step*
    all_goals try (change 4≤value.to_slice.val.length;omega)
    all_goals apply Subtype.ext
    all_goals simpa only [List.slice,value,Array.to_slice,List.drop_zero,selected] using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call
#print axioms first

theorem b4 : Array.index_usize value 4#usize=ok 1#u8 := by unfold value;rfl
theorem b5 : Array.index_usize value 5#usize=ok 1#u8 := by unfold value;rfl
theorem b6 : Array.index_usize value 6#usize=ok 1#u8 := by unfold value;rfl
theorem b7 : Array.index_usize value 7#usize=ok 0#u8 := by unfold value;rfl
#print axioms b4
#print axioms b5
#print axioms b6
#print axioms b7
end AspisR1.NFY_JHd_RequestHead
-- END copied JHd_RequestHead
-- BEGIN copied JHd_RequestSegments: lean/JHd_RequestSegments.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestSegments
open Aeneas Aeneas.Std Result
open NFY_JHd_RequestWindow
theorem w0 : (window 104 8 (by decide)).val=NFY_JFu_PublicMeta07.bytes := by rfl
#print axioms w0
theorem w1 : (window 112 32 (by decide)).val=NFY_JFs_Cell04.bytes := by rfl
#print axioms w1
theorem w2 : (window 144 32 (by decide)).val=NFY_JFs_Cell05.bytes := by rfl
#print axioms w2
theorem w3 : (window 176 8 (by decide)).val=NFY_JFs_Cell06.bytes := by rfl
#print axioms w3
theorem w4 : (window 184 32 (by decide)).val=NFY_JFu_PublicDigest43.bytes := by rfl
#print axioms w4
theorem w5 : (window 216 32 (by decide)).val=NFY_JFu_PublicDigest44.bytes := by rfl
#print axioms w5
theorem w6 : (window 248 4 (by decide)).val=NFY_JFs_Cell07.bytes := by rfl
#print axioms w6
theorem w7 : (window 252 4 (by decide)).val=NFY_JFu_PublicMeta08.bytes := by rfl
#print axioms w7
theorem w8 : (window 256 32 (by decide)).val=NFY_JFu_PublicDigest45.bytes := by rfl
#print axioms w8
theorem w9 : (window 288 32 (by decide)).val=NFY_JFu_PublicDigest46.bytes := by rfl
#print axioms w9
theorem split (xs : List U8) (off : Nat) :
    (xs.drop off).take 216 =
    (xs.drop off).take 8 ++ (xs.drop (off+8)).take 32 ++
    (xs.drop (off+40)).take 32 ++ (xs.drop (off+72)).take 8 ++
    (xs.drop (off+80)).take 32 ++ (xs.drop (off+112)).take 32 ++
    (xs.drop (off+144)).take 4 ++ (xs.drop (off+148)).take 4 ++
    (xs.drop (off+152)).take 32 ++ (xs.drop (off+184)).take 32 := by
  have cut (ys : List U8) (a b : Nat) : ys.take (a+b)=ys.take a ++ (ys.drop a).take b :=
    List.take_add
  rw [show 216=184+32 from rfl,cut,show 184=152+32 from rfl,cut,
    show 152=148+4 from rfl,cut,show 148=144+4 from rfl,cut,
    show 144=112+32 from rfl,cut,show 112=80+32 from rfl,cut,
    show 80=72+8 from rfl,cut,show 72=40+32 from rfl,cut,
    show 40=8+32 from rfl,cut]
  simp only [List.drop_drop]
#print axioms split

attribute [local irreducible] NFY_JFx_NativeBytes.publicInput NFY_JHb_DataRequest.bytes

theorem payment : window 104 216 (by decide)=NFY_JFu_PublicRange.payment := by
  apply Subtype.ext
  dsimp only [window,NFY_JFu_PublicRange.payment,NFY_JFu_PublicRange.segment]
  rw [split,split]
  simp only [Nat.reduceAdd]
  have h0:=w0;have h1:=w1;have h2:=w2;have h3:=w3;have h4:=w4
  have h5:=w5;have h6:=w6;have h7:=w7;have h8:=w8;have h9:=w9
  dsimp only [window] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,
    NFY_JFu_PublicMeta07.selected,NFY_JFs_Cell04.selected,NFY_JFs_Cell05.selected,NFY_JFs_Cell06.selected,
    NFY_JFu_PublicDigest43.selected,NFY_JFu_PublicDigest44.selected,NFY_JFs_Cell07.selected,
    NFY_JFu_PublicMeta08.selected,NFY_JFu_PublicDigest45.selected,NFY_JFu_PublicDigest46.selected]
#print axioms payment
end AspisR1.NFY_JHd_RequestSegments
-- END copied JHd_RequestSegments
-- BEGIN copied JHd_RequestSuffix: lean/JHd_RequestSuffix.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestSuffix
open Aeneas Aeneas.Std Result WP NFY_JHd_RequestWindow
attribute [local irreducible] value NFY_JHb_DataRequest.bytes NFY_JFu_PublicRange.payment

theorem source : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
    value {start:=104#usize}=ok NFY_JFu_PublicRange.payment := by
  have size : value.to_slice.val.length=320 := by
    simp only [value,Array.to_slice]
    exact NFY_JHb_DataRequest.length
  have take : (NFY_JHb_DataRequest.bytes.drop 104).take 216=NFY_JHb_DataRequest.bytes.drop 104 :=
    List.take_of_length_le (by rw [List.length_drop,NFY_JHb_DataRequest.length])
  have spec : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFromUsizeSlice U8))
      value {start:=104#usize} ⦃ out => out=window 104 216 (by decide) ⦄ := by
    unfold core.array.Array.index core.ops.index.IndexSlice core.slice.index.Slice.index
    step*
    all_goals try (change 104≤value.to_slice.val.length;omega)
    all_goals apply Subtype.ext
    all_goals simpa only [List.slice,value,Array.to_slice,window,
      show 320-104=216 from rfl,take]
      using out_post1
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same,NFY_JHd_RequestSegments.payment] at call
  exact call
#print axioms source
end AspisR1.NFY_JHd_RequestSuffix
-- END copied JHd_RequestSuffix
-- BEGIN copied JHd_RequestDecode: lean/JHd_RequestDecode.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestDecode
open Aeneas Aeneas.Std Result
open AspisR20Request pool_v1.pair_forest_terminal
attribute [local irreducible] NFY_JHd_RequestWindow.value NFY_JHd_RequestValue.value

theorem source : decode_pool_v1_pair_forest_terminal_request_reference_v1
    NFY_JHd_RequestWindow.value=ok (.Ok NFY_JHd_RequestValue.value) := by
  have size : Slice.len NFY_JHd_RequestWindow.value.to_slice=320#usize := by
    have h : NFY_JHd_RequestWindow.value.to_slice.val.length=320 := by
      simp only [NFY_JHd_RequestWindow.value,Array.to_slice]
      exact NFY_JHb_DataRequest.length
    scalar_tac
  have reqSize : POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES=ok 320#usize := by
    unfold POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_BYTES pool_v1.payment_relation.POOL_V1_PAYMENT_STATEMENT_BYTES
    rw [AdapterRw.Scalar.mul_eq 3#usize 32#usize 96#usize (by scalar_tac),bind_tc_ok,
      AdapterRw.Scalar.add_eq 8#usize 96#usize 104#usize (by scalar_tac),bind_tc_ok]
    exact AdapterRw.Scalar.add_eq _ _ _ (by scalar_tac)
  have magic : Slice.Insts.CoreCmpPartialEqArray.ne core.cmp.PartialEqU8
      NFY_JHd_RequestHead.magic POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC=ok false := by
    unfold POOL_V1_PAIR_FOREST_TERMINAL_REQUEST_MAGIC NFY_JHd_RequestHead.magic
    rfl
  have kind : transition_kind 1#u8=ok (.Ok pool_v1.historical_anchor.PoolV1TransitionKind.PrivateTransfer) := by
    unfold transition_kind
    rfl
  unfold decode_pool_v1_pair_forest_terminal_request_reference_v1
  simp only [lift,reqSize,bind_tc_ok,size,
    show (320#usize !=320#usize)=false from rfl,Bool.false_eq_true,↓reduceIte,
    NFY_JHd_RequestHead.first,magic,NFY_JHd_RequestHead.b4,NFY_JHd_RequestHead.b5,
    NFY_JHd_RequestHead.b6,NFY_JHd_RequestHead.b7,
    POOL_V1_PAIR_FOREST_TERMINAL_VERSION,pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION,
    show (1#u8 !=1#u8)=false from rfl,show (0#u8 !=0#u8)=false from rfl,
    kind,core.result.Result.Insts.CoreOpsTry.branch,REQUEST_PAYMENT_OFFSET,
    NFY_JHd_RequestSuffix.source,NFY_JHd_RequestPayload.source,AspisR20Request.core.result.Result.map_err]
  simp only [REQUEST_PROFILE_OFFSET,REQUEST_RELEASE_OFFSET,REQUEST_POOL_PROGRAM_OFFSET,
    NFY_JHd_RequestBindings.profile,NFY_JHd_RequestBindings.release,NFY_JHd_RequestBindings.pool,
    NFY_JHd_RequestBindings.profile_cast,NFY_JHd_RequestBindings.release_cast,NFY_JHd_RequestBindings.pool_cast,
    bind_tc_ok,AspisR20Request.core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    NFY_JHd_RequestValue.profile_nonzero,NFY_JHd_RequestValue.release_nonzero,NFY_JHd_RequestValue.pool_nonzero,
    Bool.false_eq_true,↓reduceIte]
  unfold NFY_JHd_RequestValue.value
  rfl
#print axioms source
end AspisR1.NFY_JHd_RequestDecode
-- END copied JHd_RequestDecode
-- BEGIN copied JHd_RequestNative: lean/JHd_RequestNative.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHd_RequestNative
open Aeneas Aeneas.Std Result
abbrev Request := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev FormatError := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1

/-- Slice wrapper for the extracted ASQ8 reference decoder, retaining every
error constructor through the explicit carrier map. Native/reference codec
association remains a separate source obligation. -/
def decode (bytes : Slice U8) : Result (core.result.Result Request FormatError) := do
  let array ← core.array.TryFromSharedArraySlice.try_from 320#usize bytes
  match array with
  | .Err _=>ok (.Err .WrongLength)
  | .Ok array=>
    let result ← AspisR20Request.pool_v1.pair_forest_terminal.decode_pool_v1_pair_forest_terminal_request_reference_v1 array
    match result with
    | .Err error=>ok (.Err (NFY_JHd_RequestCarrier.mapPoolV1PairForestTerminalFormatErrorV1 error))
    | .Ok request=>ok (.Ok (NFY_JHd_RequestCarrier.request request))

attribute [local irreducible] NFY_JHb_DataRequest.value NFY_JHd_RequestWindow.value

theorem shared : core.array.TryFromSharedArraySlice.try_from 320#usize NFY_JHb_DataRequest.value=
    ok (.Ok NFY_JHd_RequestWindow.value) := by
  apply NFY_JFs_ArrayWindow.shared
  unfold NFY_JHb_DataRequest.value NFY_JHd_RequestWindow.value
  rfl
#print axioms shared

theorem source : decode NFY_JHb_DataRequest.value=ok (.Ok NFY_JHd_RequestCarrier.actual) := by
  unfold decode
  simp only [shared,bind_tc_ok,NFY_JHd_RequestDecode.source]
  rfl
#print axioms source
end AspisR1.NFY_JHd_RequestNative
-- END copied JHd_RequestNative
-- BEGIN copied JHf_Carrier0: lean/JHf_Carrier0.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairLiveSnapshotV1 (value : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,sequence:=value.sequence,next_pair_index:=value.next_pair_index,current_root:=value.current_root,frontier:=value.frontier}

def fromPoolV1PairLiveSnapshotV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,sequence:=value.sequence,next_pair_index:=value.next_pair_index,current_root:=value.current_root,frontier:=value.frontier}
theorem from_toPoolV1PairLiveSnapshotV1 (v : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
    fromPoolV1PairLiveSnapshotV1 (toPoolV1PairLiveSnapshotV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1]
  all_goals rfl
#print axioms from_toPoolV1PairLiveSnapshotV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier0
-- BEGIN copied JHf_Carrier1: lean/JHf_Carrier1.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairVerifiedAfterstateV1 (value : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=value.next_pair_index,next_root:=value.next_root,next_frontier:=value.next_frontier}

def fromPoolV1PairVerifiedAfterstateV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1 :=
  {next_pair_index:=value.next_pair_index,next_root:=value.next_root,next_frontier:=value.next_frontier}
theorem from_toPoolV1PairVerifiedAfterstateV1 (v : AdapterRw.aspis_statement.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
    fromPoolV1PairVerifiedAfterstateV1 (toPoolV1PairVerifiedAfterstateV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1]
  all_goals rfl
#print axioms from_toPoolV1PairVerifiedAfterstateV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier1
-- BEGIN copied JHf_Carrier2: lean/JHf_Carrier2.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairLatePublicStatementV1 (value : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=toPoolV1PairLiveSnapshotV1 (value.live_snapshot),candidate_afterstate:=toPoolV1PairVerifiedAfterstateV1 (value.candidate_afterstate)}

def fromPoolV1PairLatePublicStatementV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1 :=
  {live_snapshot:=fromPoolV1PairLiveSnapshotV1 (value.live_snapshot),candidate_afterstate:=fromPoolV1PairVerifiedAfterstateV1 (value.candidate_afterstate)}
theorem from_toPoolV1PairLatePublicStatementV1 (v : AdapterRw.aspis_statement.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
    fromPoolV1PairLatePublicStatementV1 (toPoolV1PairLatePublicStatementV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1]
  all_goals rfl
#print axioms from_toPoolV1PairLatePublicStatementV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier2
-- BEGIN copied JHf_Carrier3: lean/JHf_Carrier3.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairForestTerminalCommonV1 (value : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
  {master_account:=value.master_account,checkpoint_account:=value.checkpoint_account,selected_lane_account:=value.selected_lane_account,output_lane:=value.output_lane,checkpoint_sequence:=value.checkpoint_sequence,historical_global_anchor:=value.historical_global_anchor,lane_transition:=toPoolV1PairLatePublicStatementV1 (value.lane_transition)}

def fromPoolV1PairForestTerminalCommonV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1 :=
  {master_account:=value.master_account,checkpoint_account:=value.checkpoint_account,selected_lane_account:=value.selected_lane_account,output_lane:=value.output_lane,checkpoint_sequence:=value.checkpoint_sequence,historical_global_anchor:=value.historical_global_anchor,lane_transition:=fromPoolV1PairLatePublicStatementV1 (value.lane_transition)}
theorem from_toPoolV1PairForestTerminalCommonV1 (v : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalCommonV1) :
    fromPoolV1PairForestTerminalCommonV1 (toPoolV1PairForestTerminalCommonV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1]
  all_goals rfl
#print axioms from_toPoolV1PairForestTerminalCommonV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier3
-- BEGIN copied JHf_Carrier4: lean/JHf_Carrier4.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PrivateTransferPublicV1 (value : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,recipient_commitment:=value.recipient_commitment,change_commitment:=value.change_commitment}

def fromPoolV1PrivateTransferPublicV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,recipient_commitment:=value.recipient_commitment,change_commitment:=value.change_commitment}
theorem from_toPoolV1PrivateTransferPublicV1 (v : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
    fromPoolV1PrivateTransferPublicV1 (toPoolV1PrivateTransferPublicV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1]
  all_goals rfl
#print axioms from_toPoolV1PrivateTransferPublicV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier4
-- BEGIN copied JHf_Carrier5: lean/JHf_Carrier5.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1WithdrawalPublicV1 (value : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,amount:=value.amount,destination_token_account:=value.destination_token_account,change_commitment:=value.change_commitment}

def fromPoolV1WithdrawalPublicV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1 :=
  {pool:=value.pool,deployment_domain:=value.deployment_domain,anchor_sequence:=value.anchor_sequence,anchor_root:=value.anchor_root,nullifier:=value.nullifier,asset_id:=value.asset_id,amount:=value.amount,destination_token_account:=value.destination_token_account,change_commitment:=value.change_commitment}
theorem from_toPoolV1WithdrawalPublicV1 (v : AdapterRw.aspis_statement.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
    fromPoolV1WithdrawalPublicV1 (toPoolV1WithdrawalPublicV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1]
  all_goals rfl
#print axioms from_toPoolV1WithdrawalPublicV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier5
-- BEGIN copied JHf_Carrier6: lean/JHf_Carrier6.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairForestTerminalStatementV1 (value : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 :=
  match value with
  | .PrivateTransfer x0 x1 => AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer (toPoolV1PairForestTerminalCommonV1 (x0)) (toPoolV1PrivateTransferPublicV1 (x1))
  | .Withdrawal x0 x1 => AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal (toPoolV1PairForestTerminalCommonV1 (x0)) (toPoolV1WithdrawalPublicV1 (x1))

def fromPoolV1PairForestTerminalStatementV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1 :=
  match value with
  | .PrivateTransfer x0 x1 => AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.PrivateTransfer (fromPoolV1PairForestTerminalCommonV1 (x0)) (fromPoolV1PrivateTransferPublicV1 (x1))
  | .Withdrawal x0 x1 => AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.Withdrawal (fromPoolV1PairForestTerminalCommonV1 (x0)) (fromPoolV1WithdrawalPublicV1 (x1))
theorem from_toPoolV1PairForestTerminalStatementV1 (v : AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1) :
    fromPoolV1PairForestTerminalStatementV1 (toPoolV1PairForestTerminalStatementV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1]
  all_goals rfl
#print axioms from_toPoolV1PairForestTerminalStatementV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier6
-- BEGIN copied JHf_Carrier7: lean/JHf_Carrier7.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolIdentityV1 (value : AdapterRw.aspis_statement.pool_v1.format.PoolIdentityV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.PoolIdentityV1 :=
  {pool:=value.pool,asset_mint:=value.asset_mint,token_program:=value.token_program,asset_id:=value.asset_id,deployment_domain:=value.deployment_domain}
def fromPoolIdentityV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.PoolIdentityV1) : AdapterRw.aspis_statement.pool_v1.format.PoolIdentityV1 :=
  {pool:=value.pool,asset_mint:=value.asset_mint,token_program:=value.token_program,asset_id:=value.asset_id,deployment_domain:=value.deployment_domain}
theorem from_toPoolIdentityV1 (v : AdapterRw.aspis_statement.pool_v1.format.PoolIdentityV1) : fromPoolIdentityV1 (toPoolIdentityV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1,fromPoolIdentityV1,toPoolIdentityV1]
  all_goals rfl
#print axioms from_toPoolIdentityV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier7
-- BEGIN copied JHf_Carrier8: lean/JHf_Carrier8.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toVerifierPolicyV1 (value : AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.VerifierPolicyV1 :=
  {flags:=value.flags,registry_program:=value.registry_program,registry_authority:=value.registry_authority,policy_binding:=value.policy_binding}
def fromVerifierPolicyV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.format.VerifierPolicyV1) : AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1 :=
  {flags:=value.flags,registry_program:=value.registry_program,registry_authority:=value.registry_authority,policy_binding:=value.policy_binding}
theorem from_toVerifierPolicyV1 (v : AdapterRw.aspis_statement.pool_v1.format.VerifierPolicyV1) : fromVerifierPolicyV1 (toVerifierPolicyV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1,fromPoolIdentityV1,toPoolIdentityV1,fromVerifierPolicyV1,toVerifierPolicyV1]
  all_goals rfl
#print axioms from_toVerifierPolicyV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier8
-- BEGIN copied JHf_Carrier9: lean/JHf_Carrier9.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairForestMasterV1 (value : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1 :=
  {bump:=value.bump,identity:=toPoolIdentityV1 value.identity,verifier_policy:=toVerifierPolicyV1 value.verifier_policy,initialized_lane_mask:=value.initialized_lane_mask,has_checkpoint:=value.has_checkpoint,next_checkpoint_sequence:=value.next_checkpoint_sequence,last_checkpoint_lane_sequences:=value.last_checkpoint_lane_sequences}
def fromPoolV1PairForestMasterV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1 :=
  {bump:=value.bump,identity:=fromPoolIdentityV1 value.identity,verifier_policy:=fromVerifierPolicyV1 value.verifier_policy,initialized_lane_mask:=value.initialized_lane_mask,has_checkpoint:=value.has_checkpoint,next_checkpoint_sequence:=value.next_checkpoint_sequence,last_checkpoint_lane_sequences:=value.last_checkpoint_lane_sequences}
theorem from_toPoolV1PairForestMasterV1 (v : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestMasterV1) : fromPoolV1PairForestMasterV1 (toPoolV1PairForestMasterV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1,fromPoolIdentityV1,toPoolIdentityV1,fromVerifierPolicyV1,toVerifierPolicyV1,fromPoolV1PairForestMasterV1,toPoolV1PairForestMasterV1]
  all_goals rfl
#print axioms from_toPoolV1PairForestMasterV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier9
-- BEGIN copied JHf_Carrier10: lean/JHf_Carrier10.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toIncrementalMerkleTreeV1 (value : AdapterRw.aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1 :=
  {next_leaf_index:=value.next_leaf_index,root:=value.root,frontier:=value.frontier}
def fromIncrementalMerkleTreeV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1) : AdapterRw.aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1 :=
  {next_leaf_index:=value.next_leaf_index,root:=value.root,frontier:=value.frontier}
theorem from_toIncrementalMerkleTreeV1 (v : AdapterRw.aspis_statement.pool_v1.incremental_merkle.IncrementalMerkleTreeV1) : fromIncrementalMerkleTreeV1 (toIncrementalMerkleTreeV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1,fromPoolIdentityV1,toPoolIdentityV1,fromVerifierPolicyV1,toVerifierPolicyV1,fromPoolV1PairForestMasterV1,toPoolV1PairForestMasterV1,fromIncrementalMerkleTreeV1,toIncrementalMerkleTreeV1]
  all_goals rfl
#print axioms from_toIncrementalMerkleTreeV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier10
-- BEGIN copied JHf_Carrier11: lean/JHf_Carrier11.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairForestLaneStateV1 (value : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1 :=
  {bump:=value.bump,master:=value.master,lane_id:=value.lane_id,tree:=toIncrementalMerkleTreeV1 value.tree}
def fromPoolV1PairForestLaneStateV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1) : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1 :=
  {bump:=value.bump,master:=value.master,lane_id:=value.lane_id,tree:=fromIncrementalMerkleTreeV1 value.tree}
theorem from_toPoolV1PairForestLaneStateV1 (v : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestLaneStateV1) : fromPoolV1PairForestLaneStateV1 (toPoolV1PairForestLaneStateV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1,fromPoolIdentityV1,toPoolIdentityV1,fromVerifierPolicyV1,toVerifierPolicyV1,fromPoolV1PairForestMasterV1,toPoolV1PairForestMasterV1,fromIncrementalMerkleTreeV1,toIncrementalMerkleTreeV1,fromPoolV1PairForestLaneStateV1,toPoolV1PairForestLaneStateV1]
  all_goals rfl
#print axioms from_toPoolV1PairForestLaneStateV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier11
-- BEGIN copied JHf_Carrier12: lean/JHf_Carrier12.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toPoolV1PairForestCheckpointV1 (value : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1 :=
  {bump:=value.bump,master:=value.master,deployment_domain:=value.deployment_domain,checkpoint_sequence:=value.checkpoint_sequence,global_root:=value.global_root,lane_sequences:=value.lane_sequences}
def fromPoolV1PairForestCheckpointV1 (value : AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1 :=
  {bump:=value.bump,master:=value.master,deployment_domain:=value.deployment_domain,checkpoint_sequence:=value.checkpoint_sequence,global_root:=value.global_root,lane_sequences:=value.lane_sequences}
theorem from_toPoolV1PairForestCheckpointV1 (v : AdapterRw.aspis_statement.pool_v1.pair_forest_accounts.PoolV1PairForestCheckpointV1) : fromPoolV1PairForestCheckpointV1 (toPoolV1PairForestCheckpointV1 v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1,fromPoolIdentityV1,toPoolIdentityV1,fromVerifierPolicyV1,toVerifierPolicyV1,fromPoolV1PairForestMasterV1,toPoolV1PairForestMasterV1,fromIncrementalMerkleTreeV1,toIncrementalMerkleTreeV1,fromPoolV1PairForestLaneStateV1,toPoolV1PairForestLaneStateV1,fromPoolV1PairForestCheckpointV1,toPoolV1PairForestCheckpointV1]
  all_goals rfl
#print axioms from_toPoolV1PairForestCheckpointV1
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier12
-- BEGIN copied JHf_Carrier13: lean/JHf_Carrier13.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
def toAuthenticatedAsq8Accounts (value : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts) : AspisR1AdapterReconstruct.r1_pool_adapter.AuthenticatedAsq8Accounts :=
  {master_account:=value.master_account,checkpoint_account:=value.checkpoint_account,selected_lane_account:=value.selected_lane_account,master:=toPoolV1PairForestMasterV1 value.master,checkpoint:=toPoolV1PairForestCheckpointV1 value.checkpoint,selected_lane:=toPoolV1PairForestLaneStateV1 value.selected_lane,live_snapshot:=toPoolV1PairLiveSnapshotV1 value.live_snapshot}
def fromAuthenticatedAsq8Accounts (value : AspisR1AdapterReconstruct.r1_pool_adapter.AuthenticatedAsq8Accounts) : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts :=
  {master_account:=value.master_account,checkpoint_account:=value.checkpoint_account,selected_lane_account:=value.selected_lane_account,master:=fromPoolV1PairForestMasterV1 value.master,checkpoint:=fromPoolV1PairForestCheckpointV1 value.checkpoint,selected_lane:=fromPoolV1PairForestLaneStateV1 value.selected_lane,live_snapshot:=fromPoolV1PairLiveSnapshotV1 value.live_snapshot}
theorem from_toAuthenticatedAsq8Accounts (v : AdapterRw.r1_pool_adapter.AuthenticatedAsq8Accounts) : fromAuthenticatedAsq8Accounts (toAuthenticatedAsq8Accounts v)=v := by
  cases v <;> simp only [fromPoolV1PairLiveSnapshotV1,toPoolV1PairLiveSnapshotV1,fromPoolV1PairVerifiedAfterstateV1,toPoolV1PairVerifiedAfterstateV1,fromPoolV1PairLatePublicStatementV1,toPoolV1PairLatePublicStatementV1,fromPoolV1PairForestTerminalCommonV1,toPoolV1PairForestTerminalCommonV1,fromPoolV1PrivateTransferPublicV1,toPoolV1PrivateTransferPublicV1,fromPoolV1WithdrawalPublicV1,toPoolV1WithdrawalPublicV1,fromPoolV1PairForestTerminalStatementV1,toPoolV1PairForestTerminalStatementV1,fromPoolIdentityV1,toPoolIdentityV1,fromVerifierPolicyV1,toVerifierPolicyV1,fromPoolV1PairForestMasterV1,toPoolV1PairForestMasterV1,fromIncrementalMerkleTreeV1,toIncrementalMerkleTreeV1,fromPoolV1PairForestLaneStateV1,toPoolV1PairForestLaneStateV1,fromPoolV1PairForestCheckpointV1,toPoolV1PairForestCheckpointV1,fromAuthenticatedAsq8Accounts,toAuthenticatedAsq8Accounts]
  all_goals rfl
#print axioms from_toAuthenticatedAsq8Accounts
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier13
-- BEGIN copied JHf_Carrier14: lean/JHf_Carrier14.lean
set_option autoImplicit false
namespace AspisR1.JHf_Carrier
open Aeneas Aeneas.Std Result
abbrev Payment := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1
abbrev RawPayment := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalPaymentV1

def toPayment : Payment → RawPayment
  | .PrivateTransfer p=>.PrivateTransfer (toPoolV1PrivateTransferPublicV1 p)
  | .Withdrawal p=>.Withdrawal (toPoolV1WithdrawalPublicV1 p)
def fromPayment : RawPayment → Payment
  | .PrivateTransfer p=>.PrivateTransfer (fromPoolV1PrivateTransferPublicV1 p)
  | .Withdrawal p=>.Withdrawal (fromPoolV1WithdrawalPublicV1 p)

theorem from_toPayment (p : Payment) : fromPayment (toPayment p)=p := by
  cases p <;> simp only [fromPayment,toPayment,from_toPoolV1PrivateTransferPublicV1,from_toPoolV1WithdrawalPublicV1]
#print axioms from_toPayment

abbrev Request := AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
abbrev RawRequest := AspisR1AdapterReconstruct.aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalRequestV1
def toRequest (r : Request) : RawRequest :=
  ⟨r.verifier_profile,r.verifier_release,r.pool_program,toPayment r.«public»⟩
def fromRequest (r : RawRequest) : Request :=
  ⟨r.verifier_profile,r.verifier_release,r.pool_program,fromPayment r.«public»⟩
theorem from_toRequest (r : Request) : fromRequest (toRequest r)=r := by
  cases r
  simp only [fromRequest,toRequest,from_toPayment]
#print axioms from_toRequest
end AspisR1.JHf_Carrier
-- END copied JHf_Carrier14
-- BEGIN copied JHf_ProgramErrorCarrier: lean/JHf_ProgramErrorCarrier.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHf_ProgramErrorCarrier
open Aeneas Aeneas.Std Result
def toRaw (e : AdapterRw.solana_program_error.ProgramError) : AspisR1AdapterReconstruct.solana_program_error.ProgramError :=
  match e with
  | .Custom v=>.Custom v
  | .InvalidArgument=>.InvalidArgument
  | .InvalidInstructionData=>.InvalidInstructionData
  | .InvalidAccountData=>.InvalidAccountData
  | .AccountDataTooSmall=>.AccountDataTooSmall
  | .InsufficientFunds=>.InsufficientFunds
  | .IncorrectProgramId=>.IncorrectProgramId
  | .MissingRequiredSignature=>.MissingRequiredSignature
  | .AccountAlreadyInitialized=>.AccountAlreadyInitialized
  | .UninitializedAccount=>.UninitializedAccount
  | .NotEnoughAccountKeys=>.NotEnoughAccountKeys
  | .AccountBorrowFailed=>.AccountBorrowFailed
  | .MaxSeedLengthExceeded=>.MaxSeedLengthExceeded
  | .InvalidSeeds=>.InvalidSeeds
  | .BorshIoError v=>.BorshIoError v
  | .AccountNotRentExempt=>.AccountNotRentExempt
  | .UnsupportedSysvar=>.UnsupportedSysvar
  | .IllegalOwner=>.IllegalOwner
  | .MaxAccountsDataAllocationsExceeded=>.MaxAccountsDataAllocationsExceeded
  | .InvalidRealloc=>.InvalidRealloc
  | .MaxInstructionTraceLengthExceeded=>.MaxInstructionTraceLengthExceeded
  | .BuiltinProgramsMustConsumeComputeUnits=>.BuiltinProgramsMustConsumeComputeUnits
  | .InvalidAccountOwner=>.InvalidAccountOwner
  | .ArithmeticOverflow=>.ArithmeticOverflow
  | .Immutable=>.Immutable
  | .IncorrectAuthority=>.IncorrectAuthority
def fromRaw (e : AspisR1AdapterReconstruct.solana_program_error.ProgramError) : AdapterRw.solana_program_error.ProgramError :=
  match e with
  | .Custom v=>.Custom v
  | .InvalidArgument=>.InvalidArgument
  | .InvalidInstructionData=>.InvalidInstructionData
  | .InvalidAccountData=>.InvalidAccountData
  | .AccountDataTooSmall=>.AccountDataTooSmall
  | .InsufficientFunds=>.InsufficientFunds
  | .IncorrectProgramId=>.IncorrectProgramId
  | .MissingRequiredSignature=>.MissingRequiredSignature
  | .AccountAlreadyInitialized=>.AccountAlreadyInitialized
  | .UninitializedAccount=>.UninitializedAccount
  | .NotEnoughAccountKeys=>.NotEnoughAccountKeys
  | .AccountBorrowFailed=>.AccountBorrowFailed
  | .MaxSeedLengthExceeded=>.MaxSeedLengthExceeded
  | .InvalidSeeds=>.InvalidSeeds
  | .BorshIoError v=>.BorshIoError v
  | .AccountNotRentExempt=>.AccountNotRentExempt
  | .UnsupportedSysvar=>.UnsupportedSysvar
  | .IllegalOwner=>.IllegalOwner
  | .MaxAccountsDataAllocationsExceeded=>.MaxAccountsDataAllocationsExceeded
  | .InvalidRealloc=>.InvalidRealloc
  | .MaxInstructionTraceLengthExceeded=>.MaxInstructionTraceLengthExceeded
  | .BuiltinProgramsMustConsumeComputeUnits=>.BuiltinProgramsMustConsumeComputeUnits
  | .InvalidAccountOwner=>.InvalidAccountOwner
  | .ArithmeticOverflow=>.ArithmeticOverflow
  | .Immutable=>.Immutable
  | .IncorrectAuthority=>.IncorrectAuthority
theorem from_to (e : AdapterRw.solana_program_error.ProgramError) : fromRaw (toRaw e)=e := by
  cases e <;> rfl
#print axioms from_to

theorem to_from (e : AspisR1AdapterReconstruct.solana_program_error.ProgramError) : toRaw (fromRaw e)=e := by
  cases e <;> rfl
#print axioms to_from
end AspisR1.NFY_JHf_ProgramErrorCarrier
-- END copied JHf_ProgramErrorCarrier
-- BEGIN copied JHf_RawStatementDomainGuard: lean/JHf_RawStatementDomainGuard.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHf_RawStatementDomainGuard
open Aeneas Aeneas.Std Result
open AspisR1AdapterReconstruct aspis_statement.pool_v1.pair_forest_terminal

def paymentDomain : PoolV1PairForestTerminalStatementV1 → Array U8 32#usize
  | .PrivateTransfer _ p=>p.deployment_domain
  | .Withdrawal _ p=>p.deployment_domain

def liveDomain : PoolV1PairForestTerminalStatementV1 → Array U8 32#usize
  | .PrivateTransfer c _=>c.lane_transition.live_snapshot.deployment_domain
  | .Withdrawal c _=>c.lane_transition.live_snapshot.deployment_domain

theorem source (statement : PoolV1PairForestTerminalStatementV1)
    (accepted : validate_pool_v1_pair_forest_terminal_statement_v1 statement=ok (.Ok ())) :
    core.array.equality.PartialEqArray.ne core.cmp.PartialEqU8
      (paymentDomain statement) (liveDomain statement)=ok false := by
  cases statement <;> unfold validate_pool_v1_pair_forest_terminal_statement_v1 at accepted
  all_goals simp only [PoolV1PairForestTerminalStatementV1.common,statement_public_common,
    paymentDomain,liveDomain,bind_tc_ok,Bind.bind,Aeneas.Std.bind,
    core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
    core.convert.FromSame.from] at accepted ⊢
  all_goals generalize Array.repeat 32#usize 0#u8 = zero_bindings at accepted
  all_goals generalize Array.repeat 1520#usize 0#u8 = late_buffer at accepted
  all_goals repeat' first
    | (solve | assumption)
    | (solve | cases accepted)
    | (rw [if_pos (show true = true from rfl)] at accepted)
    | (rw [if_neg (show ¬ (false = true) by decide)] at accepted)
    | (dsimp only [Aeneas.Std.uncurry] at accepted)
    | (s2k_unpair <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | (s2k_uncase <;> simp_all only [Result.ok.injEq,Prod.mk.injEq])
    | s2k_unbool
    | (split at accepted)
#print axioms source
end AspisR1.NFY_JHf_RawStatementDomainGuard
-- END copied JHf_RawStatementDomainGuard
-- BEGIN copied JHb_DataMaster: lean/JHb_DataMaster.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHb_DataMaster
open Aeneas Aeneas.Std
def c00 : List U8 := [65#u8,83#u8,77#u8,56#u8,2#u8,8#u8,1#u8,254#u8,65#u8,83#u8,80#u8,73#u8,83#u8,70#u8,79#u8,82#u8,69#u8,83#u8,84#u8,56#u8,2#u8,2#u8,2#u8,8#u8,1#u8,20#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem c00_length : c00.length=32 := by simp only [c00,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c00_length
def c01 : List U8 := [0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,43#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,255#u8,1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem c01_length : c01.length=32 := by simp only [c01,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c01_length
def c02 : List U8 := [65#u8,83#u8,80#u8,73#u8,1#u8,0#u8,0#u8,0#u8,34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8]
theorem c02_length : c02.length=32 := by simp only [c02,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c02_length
def c03 : List U8 := [182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8]
theorem c03_length : c03.length=32 := by simp only [c03,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c03_length
def c04 : List U8 := [66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,66#u8,6#u8,221#u8,246#u8,225#u8,215#u8,101#u8,161#u8,147#u8,217#u8,203#u8,225#u8,70#u8,206#u8,235#u8,121#u8,172#u8,28#u8,180#u8,133#u8,237#u8,95#u8,91#u8,55#u8,145#u8]
theorem c04_length : c04.length=32 := by simp only [c04,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c04_length
def c05 : List U8 := [58#u8,140#u8,245#u8,133#u8,126#u8,255#u8,0#u8,169#u8,77#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem c05_length : c05.length=32 := by simp only [c05,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c05_length
def c06 : List U8 := [34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,65#u8,83#u8,80#u8,80#u8,1#u8,3#u8,0#u8,0#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8]
theorem c06_length : c06.length=32 := by simp only [c06,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c06_length
def c07 : List U8 := [68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,68#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem c07_length : c07.length=32 := by simp only [c07,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c07_length
def c08 : List U8 := [0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8]
theorem c08_length : c08.length=32 := by simp only [c08,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c08_length
def c09 : List U8 := [7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,7#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem c09_length : c09.length=32 := by simp only [c09,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c09_length
def c10 : List U8 := List.replicate 32 0#u8
theorem c10_length : c10.length=32 := by simp only [c10,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c10_length
def c11 : List U8 := List.replicate 32 0#u8
theorem c11_length : c11.length=32 := by simp only [c11,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c11_length
def bytes : List U8 := c00 ++ c01 ++ c02 ++ c03 ++ c04 ++ c05 ++ c06 ++ c07 ++ c08 ++ c09 ++ c10 ++ c11
theorem length : bytes.length=384 := by
  simp only [bytes,List.length_append,c00_length,c01_length,c02_length,c03_length,c04_length,c05_length,c06_length,c07_length,c08_length,c09_length,c10_length,c11_length]
#print axioms length
def value : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩
end AspisR1.NFY_JHb_DataMaster
-- END copied JHb_DataMaster
-- BEGIN copied JHb_DataForest: lean/JHb_DataForest.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHb_DataForest
open Aeneas Aeneas.Std
def c00 : List U8 := [65#u8,83#u8,67#u8,56#u8,2#u8,8#u8,1#u8,254#u8,34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8,242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,55#u8,157#u8,211#u8,124#u8,152#u8,170#u8,59#u8,88#u8]
theorem c00_length : c00.length=32 := by simp only [c00,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c00_length
def c01 : List U8 := [182#u8,77#u8,252#u8,152#u8,45#u8,26#u8,82#u8,63#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,34#u8,8#u8,198#u8,55#u8,61#u8,211#u8,19#u8,178#u8]
theorem c01_length : c01.length=32 := by simp only [c01,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c01_length
def c02 : List U8 := [242#u8,118#u8,165#u8,45#u8,20#u8,254#u8,147#u8,25#u8,42#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,85#u8,246#u8,62#u8,4#u8,159#u8,80#u8,117#u8,33#u8,221#u8,239#u8,128#u8,120#u8,216#u8,131#u8,141#u8,49#u8]
theorem c02_length : c02.length=32 := by simp only [c02,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c02_length
def c03 : List U8 := [99#u8,239#u8,102#u8,35#u8,253#u8,148#u8,147#u8,6#u8,128#u8,120#u8,67#u8,103#u8,86#u8,177#u8,157#u8,56#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem c03_length : c03.length=32 := by simp only [c03,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c03_length
def c04 : List U8 := List.replicate 32 0#u8
theorem c04_length : c04.length=32 := by simp only [c04,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c04_length
def c05 : List U8 := List.replicate 32 0#u8
theorem c05_length : c05.length=32 := by simp only [c05,List.length_cons,List.length_nil,List.length_replicate]
#print axioms c05_length
def bytes : List U8 := c00 ++ c01 ++ c02 ++ c03 ++ c04 ++ c05
theorem length : bytes.length=192 := by
  simp only [bytes,List.length_append,c00_length,c01_length,c02_length,c03_length,c04_length,c05_length]
#print axioms length
def value : Slice U8 := ⟨bytes,by rw [length];scalar_tac⟩
end AspisR1.NFY_JHb_DataForest
-- END copied JHb_DataForest
-- BEGIN copied JHf_DomainBytes: lean/JHf_DomainBytes.lean
set_option autoImplicit false
namespace AspisR1.NFY_JHf_DomainBytes
open Aeneas Aeneas.Std Result

/-- Native identity layout: master[64+112,64+144). -/
def master : Array U8 32#usize :=
  ⟨(NFY_JHb_DataMaster.bytes.drop 176).take 32,by decide⟩
/-- Native checkpoint layout: checkpoint[40,72). -/
def checkpoint : Array U8 32#usize :=
  ⟨(NFY_JHb_DataForest.bytes.drop 40).take 32,by decide⟩

theorem master_first : master.val[0]?=some 0#u8 := rfl
#print axioms master_first
theorem checkpoint_first : checkpoint.val[0]?=some 0#u8 := rfl
#print axioms checkpoint_first
theorem public_first : NFY_JFt_SnapshotValue.value.deployment_domain.val[0]?=some 5#u8 := rfl
#print axioms public_first

theorem mismatch : master ≠ NFY_JFt_SnapshotValue.value.deployment_domain := by
  intro same
  have h:=congrArg (fun a : Array U8 32#usize=>a.val[0]?) same
  rw [master_first,public_first] at h
  have bad : (0#u8 : U8)=5#u8 := Option.some.inj h
  exact (by decide : (0#u8 : U8) ≠ 5#u8) bad
#print axioms mismatch

theorem agrees : checkpoint=master := by apply Subtype.ext;rfl
#print axioms agrees
end AspisR1.NFY_JHf_DomainBytes
-- END copied JHf_DomainBytes

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
