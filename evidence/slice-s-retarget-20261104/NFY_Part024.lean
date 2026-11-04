import Lean
import NFY_Part006
import RPz7_S2K_AfterstateEncoding
import NFY_Part023
import NFY_Part020
import RPz7_S6NativeLateDecoderSplitV1

-- BEGIN copied NBK_AfterstateResult: lean/NBK_AfterstateResult.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBK_AfterstateResult
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_terminal

/-- Full Result on every typed input: no validation or canonicality premise. -/
theorem source (a : PoolV1PairVerifiedAfterstateV1) :
    encode_pool_v1_pair_verified_afterstate_v1 a = ok
      (match NFY_NBH_Validators.afterResult a with
      | .Ok _ => .Ok (AfterstateEncoding.bytes a)
      | .Err e => .Err e) := by
  have val := NFY_NBH_Validators.afterstate a
  cases r : NFY_NBH_Validators.afterResult a with
  | Ok u =>
    cases u
    rw [r] at val
    exact AfterstateEncoding.encode_exact a val
  | Err e =>
    rw [r] at val
    exact AfterstateStatus.rejection a e val

#print axioms source
end NFY_NBK_AfterstateResult
-- END copied NBK_AfterstateResult
-- BEGIN copied NBN_FrontierDependency: lean/NBN_FrontierDependency.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_FrontierDependency
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
abbrev Digest := Array U32 8#usize
abbrev Encode := Digest → Array U8 32#usize

/-- Exact named lower bridge needed on caller-proved canonical inputs. -/
def NBN_Dep_DigestEncodeCanonical (encode : Encode) : Prop :=
  ∀ d, NBD_DigestInduction.Canonical d → encode d = DigestBytes.bytes d

/-- The unguarded first-byte helper needs the stronger all-raw lower domain. -/
def NBN_Dep_DigestEncodeRaw (encode : Encode) : Prop :=
  ∀ d, encode d = DigestBytes.bytes d

def liveFold (encode : Encode) : List Digest → Nat → Slice U8 → Slice U8
  | [],_,out => out
  | d::ds,k,out => liveFold encode ds (k+1) (out.setSlice! (160+32*k) (encode d).val)

def afterFold (encode : Encode) : List Digest → Nat → Array U8 688#usize → Array U8 688#usize
  | [],_,out => out
  | d::ds,k,out => afterFold encode ds (k+1) (out.setSlice! (48+32*k) (encode d).val)

theorem live_fold (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (ds : List Digest) (all : ∀ d ∈ ds, NBD_DigestInduction.Canonical d)
    (k : Nat) (out : Slice U8) :
    liveFold encode ds k out = NFY_NBK_LiveBytes.fold ds k out := by
  induction ds generalizing k out with
  | nil => rfl
  | cons d ds ih =>
    have first := lower d (all d (by simp))
    simp only [liveFold,NFY_NBK_LiveBytes.fold,first]
    exact ih (fun x hx => all x (by simp [hx])) (k+1) _

theorem after_fold (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (ds : List Digest) (all : ∀ d ∈ ds, NBD_DigestInduction.Canonical d)
    (k : Nat) (out : Array U8 688#usize) :
    afterFold encode ds k out = AfterstateBytes.fold ds k out := by
  induction ds generalizing k out with
  | nil => rfl
  | cons d ds ih =>
    have first := lower d (all d (by simp))
    simp only [afterFold,AfterstateBytes.fold,first]
    exact ih (fun x hx => all x (by simp [hx])) (k+1) _

theorem rows_canonical (rows : NBH_Frontier.Frontier)
    (all : NBH_Frontier.CanonicalFrom rows 0) :
    ∀ d ∈ rows.val, NBD_DigestInduction.Canonical d := by
  intro d mem
  obtain ⟨i,hi,same⟩ := List.mem_iff_getElem.mp mem
  have bound : i < 20 := by have := rows.property; scalar_tac
  have h := all ⟨i,bound⟩ (by omega)
  simpa only [same] using h

theorem live_caller (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : NFY_NBH_LiveValidator.Snapshot) (valid : NFY_NBH_LiveValidator.result s = .Ok ())
    (out : Slice U8) :
    encode s.current_root = DigestBytes.bytes s.current_root ∧
    liveFold encode s.frontier.val 0 out = NFY_NBK_LiveBytes.fold s.frontier.val 0 out := by
  have domain := NFY_NBN_ValidatorDomains.live s valid
  exact ⟨lower _ domain.2.2.2.2.1,
    live_fold encode lower _ (rows_canonical _ domain.2.2.2.2.2) 0 out⟩

theorem after_caller (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (a : NFY_NBH_Validators.Afterstate) (valid : NFY_NBH_Validators.afterResult a = .Ok ())
    (out : Array U8 688#usize) :
    encode a.next_root = DigestBytes.bytes a.next_root ∧
    afterFold encode a.next_frontier.val 0 out = AfterstateBytes.fold a.next_frontier.val 0 out := by
  have domain := NFY_NBN_ValidatorDomains.afterstate a valid
  exact ⟨lower _ domain.2.2.1,
    after_fold encode lower _ (rows_canonical _ domain.2.2.2) 0 out⟩

#print axioms live_fold
#print axioms after_fold
#print axioms rows_canonical
#print axioms live_caller
#print axioms after_caller
end NFY_NBN_FrontierDependency
-- END copied NBN_FrontierDependency
-- BEGIN copied NBN_DigestResultDependency: lean/NBN_DigestResultDependency.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_DigestResultDependency
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
abbrev Digest := Array U32 8#usize
abbrev Encode := Digest → Result (Array U8 32#usize)

/-- Full lower law: exact output AND ok status, on each caller-proved domain. -/
def NBN_Dep_DigestEncodeCanonical (encode : Encode) : Prop :=
  ∀ d, NBD_DigestInduction.Canonical d → encode d = ok (DigestBytes.bytes d)

def NBN_Dep_DigestEncodeRaw (encode : Encode) : Prop :=
  ∀ d, encode d = ok (DigestBytes.bytes d)

def foldM {T : Type} (encode : Encode) (store : Nat → Array U8 32#usize → T → T) :
    List Digest → Nat → T → Result T
  | [],_,out => ok out
  | d::ds,k,out => do
    let b ← encode d
    foldM encode store ds (k+1) (store k b out)

def foldModel {T : Type} (store : Nat → Array U8 32#usize → T → T) :
    List Digest → Nat → T → T
  | [],_,out => out
  | d::ds,k,out => foldModel store ds (k+1) (store k (DigestBytes.bytes d) out)

theorem fold_exact {T : Type} (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (store : Nat → Array U8 32#usize → T → T) (ds : List Digest)
    (domain : ∀ d ∈ ds, NBD_DigestInduction.Canonical d) (k : Nat) (out : T) :
    foldM encode store ds k out = ok (foldModel store ds k out) := by
  induction ds generalizing k out with
  | nil => rfl
  | cons d ds ih =>
    rw [foldM,lower d (domain d (by simp))]
    simp only [bind_tc_ok,foldModel]
    exact ih (fun x hx => domain x (by simp [hx])) (k+1) _

theorem live_model (ds : List Digest) (k : Nat) (out : Slice U8) :
    foldModel (fun i b (o : Slice U8) => o.setSlice! (160+32*i) b.val) ds k out =
      NFY_NBK_LiveBytes.fold ds k out := by
  induction ds generalizing k out with
  | nil => rfl
  | cons d ds ih => exact ih (k+1) _

theorem after_model (ds : List Digest) (k : Nat) (out : Array U8 688#usize) :
    foldModel (fun i b (o : Array U8 688#usize) => o.setSlice! (48+32*i) b.val) ds k out =
      AfterstateBytes.fold ds k out := by
  induction ds generalizing k out with
  | nil => rfl
  | cons d ds ih => exact ih (k+1) _

theorem live_caller (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : NFY_NBH_LiveValidator.Snapshot) (valid : NFY_NBH_LiveValidator.result s = .Ok ()) (out : Slice U8) :
    encode s.current_root = ok (DigestBytes.bytes s.current_root) ∧
    foldM encode (fun i b (o : Slice U8) => o.setSlice! (160+32*i) b.val) s.frontier.val 0 out =
      ok (NFY_NBK_LiveBytes.fold s.frontier.val 0 out) := by
  have d := NFY_NBN_ValidatorDomains.live s valid
  refine ⟨lower _ d.2.2.2.2.1,?_⟩
  rw [fold_exact encode lower _ _ (NFY_NBN_FrontierDependency.rows_canonical _ d.2.2.2.2.2),live_model]

theorem after_caller (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : NFY_NBH_Validators.Afterstate) (valid : NFY_NBH_Validators.afterResult s = .Ok ()) (out : Array U8 688#usize) :
    encode s.next_root = ok (DigestBytes.bytes s.next_root) ∧
    foldM encode (fun i b (o : Array U8 688#usize) => o.setSlice! (48+32*i) b.val) s.next_frontier.val 0 out =
      ok (AfterstateBytes.fold s.next_frontier.val 0 out) := by
  have d := NFY_NBN_ValidatorDomains.afterstate s valid
  refine ⟨lower _ d.2.2.1,?_⟩
  rw [fold_exact encode lower _ _ (NFY_NBN_FrontierDependency.rows_canonical _ d.2.2.2),after_model]

#print axioms fold_exact
#print axioms live_model
#print axioms after_model
#print axioms live_caller
#print axioms after_caller
end NFY_NBN_DigestResultDependency
-- END copied NBN_DigestResultDependency
-- BEGIN copied NBN_EncoderSummary: lean/NBN_EncoderSummary.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBN_EncoderSummary
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_terminal
abbrev Afterstate := NFY_NBH_Validators.Afterstate
abbrev Snapshot := NFY_NBH_LiveValidator.Snapshot
abbrev Encode := NFY_NBN_DigestResultDependency.Encode
abbrev NBN_Dep_DigestEncodeCanonical := NFY_NBN_DigestResultDependency.NBN_Dep_DigestEncodeCanonical

def afterHeader (a : Afterstate) (output : Array U8 688#usize) (root : Array U8 32#usize) : Array U8 688#usize :=
  ⟨(((((((output.val.setSlice! 0 POOL_V1_PAIR_VERIFIED_AFTERSTATE_MAGIC.val).set
      4 POOL_V1_PAIR_VERIFIER_TRANSPORT_VERSION).set
      5 pool_v1.pair_tree_profile.POOL_V1_PAIR_TREE_STORAGE_FORMAT_VERSION).set
      6 pool_v1.format.POOL_V1_DIGEST_ENCODING_VERSION).set 7 1#u8).setSlice!
      8 (core.num.U64.to_le_bytes a.next_pair_index).val).setSlice!
      16 root.val), by
        simp only [List.length_setSlice!,List.length_set,output.property]⟩

def liveHeader (a : Snapshot) (output : Slice U8) (root : Array U8 32#usize) : Slice U8 :=
  ⟨((((((((output.val.setSlice! 0 pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_MAGIC.val).set
      8 pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_VERSION).setSlice!
      16 AspisR1.NFY_JFt_SnapshotConstants.formatArray.val).setSlice!
      48 a.pool.val).setSlice! 80 a.deployment_domain.val).setSlice!
      112 (core.num.U64.to_le_bytes a.sequence).val).setSlice!
      120 (core.num.U64.to_le_bytes a.next_pair_index).val).setSlice!
      128 root.val), by
        simpa only [List.length_setSlice!,List.length_set] using output.property⟩


theorem after_header (a : Afterstate) (out : Array U8 688#usize) :
    afterHeader a out (DigestBytes.bytes a.next_root) = AfterstatePrepare.value a out := by rfl

theorem live_header (a : Snapshot) (out : Slice U8) :
    liveHeader a out (DigestBytes.bytes a.current_root) = NFY_NBK_LivePrepare.value a out := by rfl

/-- Source control summary; encoded child Results retain fail/div. -/
def after (encode : Encode) (a : Afterstate) :
    Result (core.result.Result (Array U8 688#usize) PoolV1PairVerifierTransportErrorV1) :=
  match NFY_NBH_Validators.afterResult a with
  | .Err e => ok (.Err e)
  | .Ok _ => do
    let root ← encode a.next_root
    let out ← NFY_NBN_DigestResultDependency.foldM encode
      (fun i b (o : Array U8 688#usize) => o.setSlice! (48+32*i) b.val)
      a.next_frontier.val 0 (afterHeader a (Array.repeat 688#usize 0#u8) root)
    ok (.Ok out)

def live (encode : Encode) (s : Snapshot) (out : Slice U8) :
    Result (core.result.Result Unit pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotErrorV1 × Slice U8) :=
  if out.length ≠ 800 then ok (.Err .WrongLength,out)
  else match NFY_NBH_LiveValidator.result s with
    | .Err e => ok (.Err e,out)
    | .Ok _ => do
      let root ← encode s.current_root
      let written ← NFY_NBN_DigestResultDependency.foldM encode
        (fun i b (o : Slice U8) => o.setSlice! (160+32*i) b.val)
        s.frontier.val 0 (liveHeader s NFY_NBK_LiveResult.zero root)
      ok (.Ok (),written)

theorem after_source (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode) (a : Afterstate) :
    after encode a = encode_pool_v1_pair_verified_afterstate_v1 a := by
  rw [NFY_NBK_AfterstateResult.source]
  cases valid : NFY_NBH_Validators.afterResult a with
  | Err e => simp only [after,valid]
  | Ok u =>
    cases u
    simp only [after,valid]
    let prepared := AfterstatePrepare.value a (Array.repeat 688#usize 0#u8)
    have calls := NFY_NBN_DigestResultDependency.after_caller encode lower a valid prepared
    rw [calls.1]
    simp only [bind_tc_ok,after_header]
    rw [calls.2]
    rfl

theorem live_source (encode : Encode) (lower : NBN_Dep_DigestEncodeCanonical encode)
    (s : Snapshot) (out : Slice U8) :
    live encode s out = pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 s out := by
  rw [NFY_NBK_LiveResult.source]
  by_cases size : out.length = 800
  · simp only [live,size,ne_eq,not_true_eq_false,if_false]
    cases valid : NFY_NBH_LiveValidator.result s with
    | Err e => rfl
    | Ok u =>
      cases u
      let prepared := NFY_NBK_LivePrepare.value s NFY_NBK_LiveResult.zero
      have calls := NFY_NBN_DigestResultDependency.live_caller encode lower s valid prepared
      rw [calls.1]
      simp only [bind_tc_ok,live_header]
      rw [calls.2]
      rfl
  · simp only [live,size,ne_eq,not_false_eq_true,if_true]

#print axioms after_header
#print axioms live_header
#print axioms after_source
#print axioms live_source
end NFY_NBN_EncoderSummary
-- END copied NBN_EncoderSummary
-- BEGIN copied JFt_Index: lean/JFt_Index.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFt_Index
open Aeneas Aeneas.Std Result WP

theorem source (bytes : Slice U8) (i : Usize) (bound : i.val<bytes.length)
    (byte : U8) (selected : bytes.val[i.val]?=some byte) :
    Slice.index_usize bytes i=ok byte := by
  have spec : Slice.index_usize bytes i ⦃ out => out=byte ⦄ := by
    step*
    trace_state
    simp_all
  obtain ⟨out,call,same⟩:=WP.spec_imp_exists spec
  rw [same] at call
  exact call

/-- Reads one of the small checked metadata windows, without reducing public1880. -/
theorem window (off n index : Nat) (bound : off+n≤1880) (inside : index<n)
    (i : Usize) (same : i.val=index) (byte : U8) (xs : List U8)
    (selected : (NFY_JFx_NativeBytes.publicInput.val.drop off).take n=xs)
    (value : xs[index]?=some byte) :
    Slice.index_usize (NFY_JFu_PublicRange.segment off n bound) i=ok byte := by
  apply source _ i (by rw [NFY_JFu_PublicRange.length,same];exact inside) byte
  change ((NFY_JFx_NativeBytes.publicInput.val.drop off).take n)[i.val]?=some byte
  rw [selected,same]
  exact value

#print axioms source
#print axioms window
end AspisR1.NFY_JFt_Index
-- END copied JFt_Index
-- BEGIN copied JFs_IndexWindow: lean/JFs_IndexWindow.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_IndexWindow
open Aeneas Aeneas.Std Result

theorem source (off n small : Nat) (bound : off+n≤1880)
    (i : Usize) (inside : i.val<n) (insideSmall : i.val<small)
    (byte : U8) (xs : List U8)
    (selected : (NFY_JFx_NativeBytes.publicInput.val.drop off).take small=xs)
    (value : xs[i.val]?=some byte) :
    Slice.index_usize (NFY_JFu_PublicRange.segment off n bound) i=ok byte := by
  apply NFY_JFt_Index.source _ _ (by rw [NFY_JFu_PublicRange.length];exact inside) byte
  dsimp only [NFY_JFu_PublicRange.segment]
  rw [List.getElem?_take_of_lt inside]
  have h:=congrArg (fun ys : List U8 => ys[i.val]?) selected
  rw [List.getElem?_take_of_lt insideSmall] at h
  exact h.trans value

#print axioms source
end AspisR1.NFY_JFs_IndexWindow
-- END copied JFs_IndexWindow
-- BEGIN copied JFu_PublicMeta00: lean/JFu_PublicMeta00.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFu_PublicMeta00
open Aeneas Aeneas.Std Result

def bytes : List U8 := [65#u8,83#u8,80#u8,76#u8,65#u8,84#u8,69#u8,49#u8,1#u8,2#u8,32#u8,0#u8,32#u8,3#u8,0#u8,0#u8,176#u8,2#u8,0#u8,0#u8,240#u8,5#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]
theorem length : bytes.length=32 := by simp only [bytes,List.length_cons,List.length_nil]

theorem selected : (NFY_JFx_NativeBytes.publicInput.val.drop 144).take 32=bytes := by
  change (NFY_JFx_DataPublic00.bytes.drop 144).take 32=bytes
  simp only [NFY_JFx_DataPublic00.bytes,NFY_JFx_DataPublic00.c00_length,NFY_JFx_DataPublic00.c01_length,NFY_JFx_DataPublic00.c02_length,NFY_JFx_DataPublic00.c03_length,NFY_JFx_DataPublic00.c04_length,NFY_JFx_DataPublic00.c05_length,NFY_JFx_DataPublic00.c06_length,NFY_JFx_DataPublic00.c07_length,NFY_JFx_DataPublic00.c08_length,NFY_JFx_DataPublic00.c09_length,NFY_JFx_DataPublic00.c10_length,NFY_JFx_DataPublic00.c11_length,NFY_JFx_DataPublic00.c12_length,NFY_JFx_DataPublic00.c13_length,NFY_JFx_DataPublic00.c14_length,NFY_JFx_DataPublic00.c15_length,NFY_JFx_DataPublic00.c16_length,NFY_JFx_DataPublic00.c17_length,NFY_JFx_DataPublic00.c18_length,NFY_JFx_DataPublic00.c19_length,NFY_JFx_DataPublic00.c20_length,NFY_JFx_DataPublic00.c21_length,NFY_JFx_DataPublic00.c22_length,NFY_JFx_DataPublic00.c23_length,NFY_JFx_DataPublic00.c24_length,NFY_JFx_DataPublic00.c25_length,NFY_JFx_DataPublic00.c26_length,NFY_JFx_DataPublic00.c27_length,NFY_JFx_DataPublic00.c28_length,NFY_JFx_DataPublic00.c29_length,NFY_JFx_DataPublic00.c30_length,NFY_JFx_DataPublic00.c31_length,NFY_JFx_DataPublic00.c32_length,NFY_JFx_DataPublic00.c33_length,NFY_JFx_DataPublic00.c34_length,NFY_JFx_DataPublic00.c35_length,NFY_JFx_DataPublic00.c36_length,NFY_JFx_DataPublic00.c37_length,NFY_JFx_DataPublic00.c38_length,NFY_JFx_DataPublic00.c39_length,NFY_JFx_DataPublic00.c40_length,NFY_JFx_DataPublic00.c41_length,NFY_JFx_DataPublic00.c42_length,NFY_JFx_DataPublic00.c43_length,NFY_JFx_DataPublic00.c44_length,NFY_JFx_DataPublic00.c45_length,NFY_JFx_DataPublic00.c46_length,NFY_JFx_DataPublic00.c47_length,NFY_JFx_DataPublic00.c48_length,NFY_JFx_DataPublic00.c49_length,NFY_JFx_DataPublic00.c50_length,NFY_JFx_DataPublic00.c51_length,NFY_JFx_DataPublic00.c52_length,NFY_JFx_DataPublic00.c53_length,NFY_JFx_DataPublic00.c54_length,NFY_JFx_DataPublic00.c55_length,NFY_JFx_DataPublic00.c56_length,NFY_JFx_DataPublic00.c57_length,NFY_JFx_DataPublic00.c58_length,List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]
  rfl

theorem source : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    NFY_JFx_NativeBytes.publicInput {start:=144#usize,«end»:=176#usize}=
    ok (NFY_JFu_PublicRange.segment 144 32 (by decide)) :=
  by
    have call:=NFY_JFu_PublicRange.read 144#usize 176#usize (by decide) (by decide)
    simpa only [show (144#usize).val=144 from rfl,
      show (176#usize).val=176 from rfl,Nat.reduceSub] using call

#print axioms length
#print axioms selected
#print axioms source
end AspisR1.NFY_JFu_PublicMeta00
-- END copied JFu_PublicMeta00
-- BEGIN copied JFs_LateBytes: lean/JFs_LateBytes.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_LateBytes
open Aeneas Aeneas.Std Result

def magic : Slice U8 := ⟨NFY_JFu_PublicMeta00.bytes.take 8,by simp [NFY_JFu_PublicMeta00.bytes];scalar_tac⟩
theorem magic_selected : NFY_JFu_PublicRange.segment 144 8 (by decide)=magic := by
  apply Subtype.ext
  exact NFY_JFt_LocalWindow.selected 144 32 0 8 (by decide) (by decide) _ NFY_JFu_PublicMeta00.selected

theorem b8 : Slice.index_usize NFY_JFu_PublicRange.late 8#usize=ok 1#u8 := by
  exact NFY_JFs_IndexWindow.source 144 1520 32 (by decide) 8#usize (by decide) (by decide)
    1#u8 NFY_JFu_PublicMeta00.bytes NFY_JFu_PublicMeta00.selected (by rfl)

theorem b9 : Slice.index_usize NFY_JFu_PublicRange.late 9#usize=ok 2#u8 := by
  exact NFY_JFs_IndexWindow.source 144 1520 32 (by decide) 9#usize (by decide) (by decide)
    2#u8 NFY_JFu_PublicMeta00.bytes NFY_JFu_PublicMeta00.selected (by rfl)

theorem b24 : Slice.index_usize NFY_JFu_PublicRange.late 24#usize=ok 0#u8 := by
  exact NFY_JFs_IndexWindow.source 144 1520 32 (by decide) 24#usize (by decide) (by decide)
    0#u8 NFY_JFu_PublicMeta00.bytes NFY_JFu_PublicMeta00.selected (by rfl)

theorem b25 : Slice.index_usize NFY_JFu_PublicRange.late 25#usize=ok 0#u8 := by
  exact NFY_JFs_IndexWindow.source 144 1520 32 (by decide) 25#usize (by decide) (by decide)
    0#u8 NFY_JFu_PublicMeta00.bytes NFY_JFu_PublicMeta00.selected (by rfl)

theorem b26 : Slice.index_usize NFY_JFu_PublicRange.late 26#usize=ok 0#u8 := by
  exact NFY_JFs_IndexWindow.source 144 1520 32 (by decide) 26#usize (by decide) (by decide)
    0#u8 NFY_JFu_PublicMeta00.bytes NFY_JFu_PublicMeta00.selected (by rfl)

theorem b27 : Slice.index_usize NFY_JFu_PublicRange.late 27#usize=ok 0#u8 := by
  exact NFY_JFs_IndexWindow.source 144 1520 32 (by decide) 27#usize (by decide) (by decide)
    0#u8 NFY_JFu_PublicMeta00.bytes NFY_JFu_PublicMeta00.selected (by rfl)

theorem b28 : Slice.index_usize NFY_JFu_PublicRange.late 28#usize=ok 0#u8 := by
  exact NFY_JFs_IndexWindow.source 144 1520 32 (by decide) 28#usize (by decide) (by decide)
    0#u8 NFY_JFu_PublicMeta00.bytes NFY_JFu_PublicMeta00.selected (by rfl)

theorem b29 : Slice.index_usize NFY_JFu_PublicRange.late 29#usize=ok 0#u8 := by
  exact NFY_JFs_IndexWindow.source 144 1520 32 (by decide) 29#usize (by decide) (by decide)
    0#u8 NFY_JFu_PublicMeta00.bytes NFY_JFu_PublicMeta00.selected (by rfl)

theorem b30 : Slice.index_usize NFY_JFu_PublicRange.late 30#usize=ok 0#u8 := by
  exact NFY_JFs_IndexWindow.source 144 1520 32 (by decide) 30#usize (by decide) (by decide)
    0#u8 NFY_JFu_PublicMeta00.bytes NFY_JFu_PublicMeta00.selected (by rfl)

theorem b31 : Slice.index_usize NFY_JFu_PublicRange.late 31#usize=ok 0#u8 := by
  exact NFY_JFs_IndexWindow.source 144 1520 32 (by decide) 31#usize (by decide) (by decide)
    0#u8 NFY_JFu_PublicMeta00.bytes NFY_JFu_PublicMeta00.selected (by rfl)

#print axioms magic_selected
#print axioms b8
#print axioms b9
#print axioms b24
#print axioms b25
#print axioms b26
#print axioms b27
#print axioms b28
#print axioms b29
#print axioms b30
#print axioms b31
end AspisR1.NFY_JFs_LateBytes
-- END copied JFs_LateBytes
-- BEGIN copied JFs_LateConstants: lean/JFs_LateConstants.lean
set_option autoImplicit false
namespace AspisR1.NFY_JFs_LateConstants
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder pool_v1.pair_tree_profile

theorem size : POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES=ok 1520#usize := by
  obtain ⟨v,call,equal⟩:=WP.spec_imp_exists AspisS6NativeLateWordCast.late_size
  exact equal ▸ call

theorem length : Slice.len NFY_JFu_PublicRange.late=1520#usize := by
  have h : NFY_JFu_PublicRange.late.length=1520 := NFY_JFu_PublicRange.length 144 1520 (by decide)
  scalar_tac

theorem magic_array : core.array.Array.index
    (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeUsizeSlice U8))
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC {start:=0#usize,«end»:=8#usize}=ok NFY_JFs_LateBytes.magic := by
  unfold POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC
  rfl

theorem magic_compare : core.cmp.PartialEq.ne.trait_default
    (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU8)
    NFY_JFs_LateBytes.magic NFY_JFs_LateBytes.magic=ok false := by rfl

#print axioms size
#print axioms length
#print axioms magic_array
#print axioms magic_compare
end AspisR1.NFY_JFs_LateConstants
-- END copied JFs_LateConstants
-- BEGIN copied NBK_LatePreflight: lean/NBK_LatePreflight.lean
set_option autoImplicit false
noncomputable section
namespace NFY_NBK_LatePreflight
open Aeneas Aeneas.Std Result
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

theorem option_ne (a b : Option U64) :
    core.cmp.PartialEq.ne.trait_default
      (core.option.Option.Insts.CoreCmpPartialEqOption core.cmp.PartialEqU64) a b =
      ok (decide (a ≠ b)) := by
  cases a <;> cases b
  all_goals simp [core.cmp.PartialEq.ne.trait_default,core.cmp.PartialEq.ne.default,
    core.option.Option.Insts.CoreCmpPartialEqOption,
    core.option.Option.Insts.CoreCmpPartialEqOption.eq,
    core.cmp.PartialEqU64,core.cmp.impls.PartialEqU64.eq,
    AspisR1TerminalDecoder.optionDiscriminant_none,
    AspisR1TerminalDecoder.optionDiscriminant_some]
  all_goals first | rfl | decide | scalar_tac

theorem wrong_length (s : PoolV1PairLatePublicStatementV1) (output : Slice U8)
    (wrong : output.length ≠ 1520) :
    encode_pool_v1_pair_late_public_statement_v1 s output = ok (.Err .WrongLength,output) := by
  have guard : (Slice.len output != 1520#usize) = true := by scalar_tac
  simp only [encode_pool_v1_pair_late_public_statement_v1,
    AspisR1.NFY_JFs_LateConstants.size,bind_tc_ok,guard,if_true]

theorem wrong_index (s : PoolV1PairLatePublicStatementV1) (output : Slice U8)
    (size : output.length = 1520)
    (wrong : U64.checked_add s.live_snapshot.next_pair_index 1#u64 ≠
      some s.candidate_afterstate.next_pair_index) :
    encode_pool_v1_pair_late_public_statement_v1 s output =
      ok (.Err .AfterstateIndexMismatch,output) := by
  have len : Slice.len output = 1520#usize := by scalar_tac
  have guard : (Slice.len output != 1520#usize) = false := by simp only [len,bne_self_eq_false]
  simp only [encode_pool_v1_pair_late_public_statement_v1,
    AspisR1.NFY_JFs_LateConstants.size,bind_tc_ok,guard,if_false,lift,option_ne,
    wrong,decide_true,if_true]
  simp [wrong]

#print axioms option_ne
#print axioms wrong_length
#print axioms wrong_index
end NFY_NBK_LatePreflight
-- END copied NBK_LatePreflight
-- BEGIN copied NBN_LatePrepare: lean/NBN_LatePrepare.lean
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NFY_NBN_LatePrepare
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def run {T : Type} (output : Slice U8) (k : Slice U8 → Result T) : Result T := do
      let (s, index_mut_back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice Std.U8) output { «end» := 8#usize }
      let s1 ← lift (Array.to_slice pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC)
      let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
      let output2 := index_mut_back s2
      let output3 ← Slice.update output2 8#usize pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION
      let output4 ← Slice.update output3 9#usize pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT
      let (s3, index_mut_back1) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output4 { start := 10#usize, «end» := 12#usize }
      let i2 ← lift (UScalar.cast .U16 pool_v1.pair_tree_profile.POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES)
      let a ← lift (core.num.U16.to_le_bytes i2)
      let s4 ← lift (Array.to_slice a)
      let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
      let output5 := index_mut_back1 s5
      let (s6, index_mut_back2) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output5 { start := 12#usize, «end» := 16#usize }
      let i3 ← lift (UScalar.cast .U32 pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES)
      let a1 ← lift (core.num.U32.to_le_bytes i3)
      let s7 ← lift (Array.to_slice a1)
      let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
      let output6 := index_mut_back2 s8
      let (s9, index_mut_back3) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output6 { start := 16#usize, «end» := 20#usize }
      let i4 ← pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES
      let i5 ← lift (UScalar.cast .U32 i4)
      let a2 ← lift (core.num.U32.to_le_bytes i5)
      let s10 ← lift (Array.to_slice a2)
      let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
      let output7 := index_mut_back3 s11
      let (s12, index_mut_back4) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output7 { start := 20#usize, «end» := 24#usize }
      let i6 ← lift (UScalar.cast .U32 1520#usize)
      let a3 ← lift (core.num.U32.to_le_bytes i6)
      let s13 ← lift (Array.to_slice a3)
      let s14 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s12 s13
      let output8 := index_mut_back4 s14
      k output8

def value (output : Slice U8) : Slice U8 :=
  ⟨((((((output.val.setSlice! 0 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC.val).set
    8 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_VERSION).set
    9 POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_ITEM_COUNT).setSlice!
    10 (core.num.U16.to_le_bytes 32#u16).val).setSlice!
    12 (core.num.U32.to_le_bytes 800#u32).val).setSlice!
    16 (core.num.U32.to_le_bytes 688#u32).val).setSlice!
    20 (core.num.U32.to_le_bytes 1520#u32).val, by
      simpa only [List.length_setSlice!,List.length_set] using output.property⟩

theorem exact {T : Type} (output : Slice U8) (size : output.length = 1520)
    (k : Slice U8 → Result T) : run output k = k (value output) := by
  have len : output.val.length = 1520 := size
  have afterSize : pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES = ok 688#usize := by
    unfold pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES pool_v1.pair_terminal.POOL_V1_PAIR_VERIFIED_AFTERSTATE_PAYLOAD_BYTES
    have h : (8#usize + 680#usize) ⦃ r => r = 688#usize ⦄ := by
      step* <;> scalar_tac
    obtain ⟨r, call, same⟩ := WP.spec_imp_exists h
    exact same ▸ call
  have cast16 : UScalar.cast .U16 32#usize = 32#u16  := by scalar_tac
  have cast800 : UScalar.cast .U32 800#usize = 800#u32  := by scalar_tac
  have cast688 : UScalar.cast .U32 688#usize = 688#u32  := by scalar_tac
  have cast1520 : UScalar.cast .U32 1520#usize = 1520#u32  := by scalar_tac
  unfold run
  simp only [AspisR1.NFY_JFs_LateConstants.size,bind_tc_ok,lift]
  simp [afterSize,cast16,cast800,cast688,cast1520, core.slice.index.Slice.index_mut, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut,
    Array.to_slice,core.slice.Slice.copy_from_slice,
    Slice.length,Slice.len,Slice.update,len,List.slice,value,
    POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_MAGIC,POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES,
    POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES]

#print axioms exact
end NFY_NBN_LatePrepare
-- END copied NBN_LatePrepare
-- BEGIN copied NBN_LateTail: lean/NBN_LateTail.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NFY_NBN_LateTail
open AspisR1TerminalDecoder AspisR1.S2K
open pool_v1.pair_tree_profile
abbrev Statement := PoolV1PairLatePublicStatementV1
abbrev Error := PoolV1PairLatePublicStatementErrorV1

def run (s : Statement) (output : Slice U8) :
    Result (core.result.Result Unit Error × Slice U8) := do
  let i7 ← 32#usize + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
  let (s15, back) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U8) output {start := 32#usize, «end» := i7}
  let (r, s16) ← encode_pool_v1_pair_live_snapshot_v1 s.live_snapshot s15
  match r with
  | .Err e => ok (.Err (.Snapshot e), back s16)
  | .Ok _ =>
    let r2 ← pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 s.candidate_afterstate
    match r2 with
    | .Err e => ok (.Err (.Afterstate e), back s16)
    | .Ok bytes =>
      let (dest, back2) ← core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeFromUsizeSlice U8) (back s16) {start := i7}
      let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 dest bytes.to_slice
      ok (.Ok (), back2 copied)

def status (s : Statement) : core.result.Result Unit Error :=
  match NFY_NBH_LiveValidator.result s.live_snapshot with
  | .Err e => .Err (.Snapshot e)
  | .Ok _ => match NFY_NBH_Validators.afterResult s.candidate_afterstate with
    | .Err e => .Err (.Afterstate e)
    | .Ok _ => .Ok ()

def value (s : Statement) (output : Slice U8) : Slice U8 :=
  match NFY_NBH_LiveValidator.result s.live_snapshot with
  | .Err _ => output
  | .Ok _ =>
    let live := output.setSlice! 32 (NFY_NBK_LiveResult.bytes s.live_snapshot).val
    match NFY_NBH_Validators.afterResult s.candidate_afterstate with
    | .Err _ => live
    | .Ok _ => live.setSlice! 832 (AfterstateEncoding.bytes s.candidate_afterstate).val

 theorem live_length (s : NFY_NBK_LiveResult.Snapshot) :
    (NFY_NBK_LiveResult.bytes s).length = 800 := by
  have fold_length (xs : List (Array U32 8#usize)) (i : Nat) (out : Slice U8) :
      (NFY_NBK_LiveBytes.fold xs i out).length = out.length := by
    induction xs generalizing i out with
    | nil => rfl
    | cons x xs ih =>
      simpa only [NFY_NBK_LiveBytes.fold, ih, Slice.length, Slice.setSlice!,List.length_setSlice!]
  simp only [NFY_NBK_LiveResult.bytes,fold_length,NFY_NBK_LivePrepare.value,
    Slice.length,NFY_NBK_LiveResult.zero,Array.to_slice,Array.repeat_val,
    List.length_setSlice!,List.length_set,List.length_replicate]
  rfl

 theorem exact (s : Statement) (output : Slice U8) (size : output.length = 1520) :
    run s output = ok (status s, value s output) := by
  have len : output.val.length = 1520 := size
  unfold run
  simp only [POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES]
  have add : 32#usize + 800#usize = ok 832#usize := by
    have h : (32#usize + 800#usize) ⦃ r => r = 832#usize ⦄ := by step*
    obtain ⟨r, call, same⟩ := WP.spec_imp_exists h
    exact same ▸ call
  rw [add]
  simp only [bind_tc_ok]
  simp [core.slice.index.Slice.index_mut,
    core.slice.index.SliceIndexRangeUsizeSlice.index_mut, Slice.length,Slice.len,len]
  rw [NFY_NBK_LiveResult.source]
  simp [Slice.length, Slice.slice,List.slice,len]
  cases hv : NFY_NBH_LiveValidator.result s.live_snapshot with
  | Err e =>
    simp [hv,status,value,bind_tc_ok]
    apply Subtype.ext
    simp only [List.setSlice!,List.length_take,List.length_drop,len]
    simp only [show min 800 (1520-32) = 800 by decide,
      show min 800 (min 800 (1520-32)) = 800 by decide]
    simp only [List.take_take,Nat.min_self]
    have restored := List.take_append_drop 800 (output.val.drop 32)
    simp only [List.drop_drop] at restored
    simpa only [List.append_assoc, restored, List.take_append_drop]
  | Ok u =>
    cases u
    simp only [hv,bind_tc_ok]
    rw [NFY_NBK_AfterstateResult.source]
    cases ha : NFY_NBH_Validators.afterResult s.candidate_afterstate with
    | Err e => simp [ha,status,value,hv,bind_tc_ok,Slice.setSlice!]
    | Ok u =>
      cases u
      simp [ha,hv,status,value,bind_tc_ok,
        core.slice.index.Slice.index_mut,core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut,
        core.slice.Slice.copy_from_slice,Array.to_slice,Slice.length,Slice.len,
        Slice.slice,List.slice,List.length_setSlice!,len,live_length,
        (AfterstateEncoding.bytes s.candidate_afterstate).property,Slice.setSlice!,lift]

#print axioms live_length
#print axioms exact
end NFY_NBN_LateTail
-- END copied NBN_LateTail
-- BEGIN copied NBN_LateFactor: lean/NBN_LateFactor.lean
set_option autoImplicit false
set_option linter.unusedSimpArgs false
open Aeneas Aeneas.Std Result
namespace NFY_NBN_LateFactor
open AspisR1TerminalDecoder
open pool_v1.pair_tree_profile

def raw (statement : PoolV1PairLatePublicStatementV1) (output : Slice U8) :
    Result (core.result.Result Unit PoolV1PairLatePublicStatementErrorV1 × Slice U8) := do
      let i7 ← 32#usize + pool_v1.pair_tree_profile.POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES
      let (s15, index_mut_back5) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeUsizeSlice Std.U8) output { start := 32#usize, «end» := i7 }
      let (r, s16) ← pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 statement.live_snapshot s15
      let r1 ← core.result.Result.map_err pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairLiveSnapshotErrorV1PoolV1PairLatePublicStatementErrorV1 r ()
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ =>
        let r2 ← pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 statement.candidate_afterstate
        let r3 ← core.result.Result.map_err pool_v1.pair_tree_profile.encode_pool_v1_pair_late_public_statement_v1.closure_1.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairVerifierTransportErrorV1PoolV1PairLatePublicStatementErrorV1 r2 ()
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r3
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val => let output9 := index_mut_back5 s16
                                                            let (s17, index_mut_back6) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U8) output9 { start := i7 }
                                                            let s18 ← lift (Array.to_slice val)
                                                            let s19 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s17 s18
                                                            let output10 := index_mut_back6 s19
                                                            ok (core.result.Result.Ok (), output10)
        | core.ops.control_flow.ControlFlow.Break residual => let r4 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual
                                                              let output9 := index_mut_back5 s16
                                                              ok (r4, output9)
      | core.ops.control_flow.ControlFlow.Break residual => let r2 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual Unit (core.convert.FromSame pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementErrorV1) residual
                                                            let output9 := index_mut_back5 s16
                                                            ok (r2, output9)


theorem bind_ext {α β : Type} (r : Result α) (f g : α → Result β)
    (h : ∀ x, f x = g x) :
    (do let x ← r; f x) = (do let x ← r; g x) := by
  cases r <;> simp_all only [bind_tc_ok,bind_tc_fail,bind_tc_div]

theorem raw_eq (s : PoolV1PairLatePublicStatementV1) (output : Slice U8) :
    raw s output = NFY_NBN_LateTail.run s output := by
  unfold raw NFY_NBN_LateTail.run
  apply bind_ext
  intro i7
  apply bind_ext
  intro window
  rcases window with ⟨input,back⟩
  apply bind_ext
  intro child
  rcases child with ⟨r,live⟩
  cases r with
  | Err e => rfl
  | Ok u =>
    cases u
    dsimp only [Aeneas.Std.uncurry]
    simp only [core.result.Result.map_err,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    apply bind_ext
    intro after
    cases after <;> rfl

#print axioms bind_ext
#print axioms raw_eq
end NFY_NBN_LateFactor
-- END copied NBN_LateFactor

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
