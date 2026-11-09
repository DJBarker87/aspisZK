import NOC_Tx1Forward
import NNH_Stage1TopCut
import NNH_Tx1SuccessfulRoute
import NNH_Tx1RouteCompare
import NNH_AccountIndexOk
import NNH_AuthSdkDistinct
import NNH_AuthGuardPorts
import NNH_AuthGuardCongr
import NNH_ModelCheckpoint
import NNH_CorrectTx2Inputs
import NNH_Stage1ZeroCurrent
import NNH_S1CodecOk
import NNH_S1HostCodec
import NNH_Stage2Sizes
import NNH_MappedOk
import NNH_ByteListInjective
import NNH_SliceEqValue
import NNH_Stage1ProofDomain
import NNH_ResultWp
import NNH_Run5bCurrentInventory
import NNX_CommonEncode
set_option autoImplicit false
noncomputable section
namespace NOC_Stage1Forward
open Aeneas Aeneas.Std Result AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries AspisR1.NOC_FinishSource

syntax "s1n" : tactic
macro_rules
 | `(tactic| s1n) => `(tactic| (noc_nrm; (try simp only [if_true, if_false, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true, eq_self_iff_true])))

abbrev S {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
 NNH_CorrectConfiguration.sdk (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation

theorem addE (a b z : Usize) (h : a.val+b.val=z.val) (s : a.val+b.val≤Usize.max) :
 (a+b : Result Usize) = ok z := AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok a b z h s
theorem mulE (a b z : Usize) (h : a.val*b.val=z.val) (s : a.val*b.val≤Usize.max) :
 (a*b : Result Usize) = ok z := AspisR1CurrentCaller.UsizeArithmetic.mul_eq_ok a b z h s
theorem subE (a b z : Usize) (h : a.val-b.val=z.val) (s : b.val≤a.val) :
 (a-b : Result Usize) = ok z := by
 have hs : (a-b : Result Usize) ⦃ x => x.val=a.val-b.val ∧ b.val≤a.val ⦄ := UScalar.sub_spec s
 obtain ⟨x,hx,hv1⟩ := WP.spec_imp_exists hs
 rw [hx]
 congr 1
 apply UScalar.eq_of_val_eq
 exact hv1.1.trans h

open _root_.AdapterRw aspis_r1_cost_probe in
theorem proofBytes : compact.PROOF_BYTES = ok 57607#usize := by
 simp only [verifier.SEMANTIC_BYTES, compact.MAX_NODES, compact.FINAL_LEN, compact.OFF_SEMANTIC,
  compact.SEMANTIC_COMPACT_VALUES, compact.LOGICAL_SEMANTIC, compact.COMPACT_SEMANTIC, compact.OFF_Y1,
  compact.COMPACT_Y1, compact.OFF_INACTIVE, compact.OFF_ROUND0, compact.OFF_FOLDED_ROOT, compact.OFF_ROUND1,
  compact.OFF_FINAL, compact.OFF_OPENINGS, compact.OPENING, compact.QUERIES, compact.OFF_NODES, compact.FIXED,
  compact.MAX_PROOF, compact.PROOF_BYTES]
 simp only [
  addE 146#usize 172#usize 318#usize (by scalar_tac) (by scalar_tac),
  mulE 2#usize 318#usize 636#usize (by scalar_tac) (by scalar_tac),
  addE 128#usize 150#usize 278#usize (by scalar_tac) (by scalar_tac),
  addE 636#usize 278#usize 914#usize (by scalar_tac) (by scalar_tac),
  mulE 32#usize 914#usize 29248#usize (by scalar_tac) (by scalar_tac),
  addE 480#usize 128#usize 608#usize (by scalar_tac) (by scalar_tac),
  addE 608#usize 32#usize 640#usize (by scalar_tac) (by scalar_tac),
  addE 640#usize 32#usize 672#usize (by scalar_tac) (by scalar_tac),
  addE 672#usize 128#usize 800#usize (by scalar_tac) (by scalar_tac),
  addE 800#usize 32#usize 832#usize (by scalar_tac) (by scalar_tac),
  mulE 22#usize 832#usize 18304#usize (by scalar_tac) (by scalar_tac),
  mulE 64#usize 32#usize 2048#usize (by scalar_tac) (by scalar_tac),
  mulE 10#usize 28#usize 280#usize (by scalar_tac) (by scalar_tac),
  addE 1#usize 280#usize 281#usize (by scalar_tac) (by scalar_tac),
  addE 87#usize 29#usize 116#usize (by scalar_tac) (by scalar_tac),
  addE 281#usize 116#usize 397#usize (by scalar_tac) (by scalar_tac),
  addE 397#usize 29#usize 426#usize (by scalar_tac) (by scalar_tac),
  mulE 16#usize 426#usize 6816#usize (by scalar_tac) (by scalar_tac),
  mulE 29#usize 32#usize 928#usize (by scalar_tac) (by scalar_tac),
  addE 12903#usize 928#usize 13831#usize (by scalar_tac) (by scalar_tac),
  subE 13831#usize 6816#usize 7015#usize (by scalar_tac) (by scalar_tac),
  addE 16#usize 7015#usize 7031#usize (by scalar_tac) (by scalar_tac),
  mulE 29#usize 16#usize 464#usize (by scalar_tac) (by scalar_tac),
  addE 7031#usize 464#usize 7495#usize (by scalar_tac) (by scalar_tac),
  addE 7495#usize 32#usize 7527#usize (by scalar_tac) (by scalar_tac),
  addE 7527#usize 224#usize 7751#usize (by scalar_tac) (by scalar_tac),
  addE 7751#usize 32#usize 7783#usize (by scalar_tac) (by scalar_tac),
  addE 7783#usize 224#usize 8007#usize (by scalar_tac) (by scalar_tac),
  addE 8007#usize 2048#usize 10055#usize (by scalar_tac) (by scalar_tac),
  addE 10055#usize 18304#usize 28359#usize (by scalar_tac) (by scalar_tac),
  addE 28359#usize 29248#usize 57607#usize (by scalar_tac) (by scalar_tac),
  bind_tc_ok]

/-- 345 public binding: the model's semantic public, carried to the current
caller, is the library's semantic public of the SAME decoded statement. -/
theorem publicBinding (st : NNH_S1HostCodec.Statement) :
 ∃ sp, aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public st = ok sp ∧
  AspisS6CurrentVerifierCarrier.toPublic sp =
  AspisR1CurrentCaller.FirstComposition.toCurrentPublic (C.semanticPublic (NNH_S1DecodeOk.carrier st)) := by
 cases st <;> exact ⟨_,rfl,by first | rfl | with_unfolding_all rfl⟩

theorem commonOk (st : NNH_S1HostCodec.Statement) :
 ∃ cm, aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common st = ok cm := by
 cases st <;> exact ⟨_,rfl⟩

theorem neFalse (s t : Slice U8) (h : s = t) :
 core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8 s t = ok false := by
 have spec := core.slice.cmp.PartialEqSlice.ne_homo_spec core.cmp.PartialEqU8 s t (by
  intro x y
  first
   | (simp [core.cmp.PartialEqU8])
   | (unfold core.cmp.PartialEqU8; simp)
   | (simp [core.cmp.PartialEqU8, bne_iff_ne]))
 obtain ⟨b,run,hb⟩ := NNH_ResultWp.expose _ _ spec
 rw [run]
 cases b
 · rfl
 · exact absurd h (hb.mp rfl)

theorem prefixRead (s : Slice U8) (n : Usize) (h : n ≤ Slice.length s) :
 ∃ out, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) s {«end» := n} = ok out ∧
  out.val = s.val.slice 0 n.val := by
 rw [Slice.index_SliceIndexRangeToUsizeSliceInst]
 unfold core.slice.index.SliceIndexRangeToUsizeSlice.index
 rw [if_pos h]
 exact ⟨_,rfl,rfl⟩

theorem indexAt (s : Slice U8) (i : Usize) (x : U8) (h : s.val[i.val]? = some x) :
 Slice.index_usize s i = ok x := by
 obtain ⟨inside,same⟩ := List.getElem?_eq_some_iff.mp h
 obtain ⟨out,run,value⟩ := NNH_ResultWp.expose _ _ (Slice.index_usize_spec s i inside)
 rw [value,same] at run
 exact run

theorem vecEq (v w : alloc.vec.Vec U8) (h : bytes (alloc.vec.Vec.deref v) = bytes (alloc.vec.Vec.deref w)) : v = w := by
 apply Subtype.ext
 exact NNH_ByteListInjective.value _ _ h

theorem mapVErrOk (a : RSL.TX1_094.Args VL) (env : RSL.Env) (s : RSL.Bytes)
 (h : NNH_Tx1ReturnedValues.mapVErrValue VL (NNH_Tx1Returns.values.tx1 a env) = .ok s) :
 NNH_Tx1Returns.value a env = .ok s := by
 change NNH_Tx1ReturnedValues.mapVErrValue VL (NNH_Tx1Returns.value a env) = .ok s at h
 cases hv : NNH_Tx1Returns.value a env with
 | ok b => rw [hv] at h; simp only [NNH_Tx1ReturnedValues.mapVErrValue] at h; exact h
 | error e => rw [hv] at h; cases h

theorem byteSame (x : U8) : NMT_345.byte x = byte x := by
 first
  | rfl
  | (show UInt8.ofNat x.val = UInt8.ofBitVec x.bv
     congr 1
     apply BitVec.eq_of_toNat_eq
     rw [BitVec.toNat_ofNat]
     exact Nat.mod_eq_of_lt x.bv.isLt)
  | (simp only [NMT_345.byte, byte]; congr 1; apply BitVec.eq_of_toNat_eq; simp)

theorem cmpLemma {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (data : Slice U8) (dataEq : bytes data = [3,10]) :
 (S c).op1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,10#u8]) = ok true := by
 have cmp := NNH_Tx1RouteCompare.source (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c) c.fixed.indexError
  c.fixed.reservation data 10#u8
 have byte10 : byte 10#u8 = 10 := by with_unfolding_all rfl
 rw [byte10,dataEq] at cmp
 rw [cmp]; simp

theorem ckLemma {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (cka : r1_pool_adapter.owned.OwnedAccount)
 (ck : RSL.OwnedAccount) (program : solana_pubkey.Pubkey) (e2 : account cka = ck)
 (co : NNH_ReturnedClone.checkpointValue ck (key program) true = .ok ()) :
 r1_pool_adapter.owned.require_verifier_checkpoint (S c) cka program true = ok (.Ok ()) := by
 have ckm := NNH_ModelCheckpoint.value
  (NNH_MRegistryOps.install (NNH_LaneModel.install (S c)) LIB_Deployed.deployed (NNH_HostCtx.envOf c)) cka program true
 rw [e2,co] at ckm
 obtain ⟨u,ckRun,_⟩ := NNH_MappedOk.value _ _ _ ckm
 cases u
 exact (NNH_AuthGuardCongr.checkpoint (S c) (NGL_CheckpointModel.install
    (NNH_MRegistryOps.install (NNH_LaneModel.install (S c)) LIB_Deployed.deployed (NNH_HostCtx.envOf c)))
    (by rfl) (by rfl) (by rfl) cka program true).trans ckRun

theorem rbLemma (a : r1_pool_adapter.owned.OwnedAccount) (o : RSL.OwnedAccount) (e : account a = o)
 (h : RSL.readonlyBuffer o = .ok ()) : r1_pool_adapter.owned.require_readonly_buffer a = ok (.Ok ()) := by
 have m := NNH_AuthGuardPorts.buffer a
 rw [e,h] at m
 obtain ⟨u,r,_⟩ := NNH_MappedOk.value _ _ _ m
 cases u; exact r

/-- The proof-account gate: header prefix equals the encoded candidate, tag S2. -/
theorem gateLemma {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (pb : Slice U8) (nat : Array U8 688#usize)
 (proofData candidate : RSL.Bytes) (pbEq : bytes pb = proofData) (lenData : proofData.length = 58295)
 (takeData : proofData.take 688 = candidate) (tagData : proofData.getD 696 0 = 2)
 (natEq : nat.val.map NMT_345.byte = candidate) :
 Slice.len pb = 58295#usize ∧
 (∃ s0, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) pb {«end» := 688#usize} = ok s0 ∧
   (S c).op0 core.cmp.PartialEqU8 s0 nat = ok false) ∧
 Slice.index_usize pb 696#usize = ok 2#u8 := by
 have pbLen : pb.val.length = 58295 := by
  rw [← lenData,← pbEq]; simp only [bytes,List.length_map]
 refine ⟨?_,?_,?_⟩
 · apply UScalar.eq_of_val_eq; change pb.val.length = _; rw [pbLen]; scalar_tac
 · obtain ⟨s0,s0Run,s0Val⟩ := prefixRead pb 688#usize (by change (688#usize).val ≤ pb.val.length; rw [pbLen]; scalar_tac)
   refine ⟨s0,s0Run,?_⟩
   have s0nat : s0 = Array.to_slice nat := by
    apply Subtype.ext
    rw [s0Val]
    show pb.val.slice 0 (688#usize).val = nat.val
    have nb : nat.val.map NMT_345.byte = nat.val.map byte := List.map_congr_left (fun x _ => byteSame x)
    have r1 : nat.val.map byte = candidate := nb.symm.trans natEq
    have hb : (pb.val.slice 0 (688#usize).val).map byte = nat.val.map byte := by
     rw [r1,← takeData,← pbEq]
     show List.map byte (List.slice 0 688 pb.val) = List.take 688 (List.map byte pb.val)
     first
      | (simp only [List.slice,List.map_take,List.drop_zero,Nat.sub_zero])
      | (simp [List.slice,List.map_take])
      | rfl
    exact NNH_ByteListInjective.value _ _ hb
   change core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8 s0 (Array.to_slice nat) = ok false
   exact neFalse _ _ s0nat
 · apply indexAt
   have h1 : (pb.val.map byte).getD 696 0 = 2 := by
    have := tagData; rw [← pbEq] at this; exact this
   have inside : 696 < pb.val.length := by rw [pbLen]; decide
   rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem inside] at h1
   simp only [Option.map_some, Option.getD_some] at h1
   have h2 : pb.val[696] = 2#u8 := by
    have := congrArg unbyte h1
    rw [byte_back] at this
    rw [this]; with_unfolding_all rfl
   show pb.val[696]? = some 2#u8
   rw [List.getElem?_eq_getElem inside]
   exact congrArg some h2

theorem fdLemma {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (st : NNH_S1HostCodec.Statement) (stmt : C.Statement)
 (stEq : NNH_S1DecodeOk.carrier st = stmt)
 (sp : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (spEq : AspisS6CurrentVerifierCarrier.toPublic sp =
  AspisR1CurrentCaller.FirstComposition.toCurrentPublic (C.semanticPublic (NNH_S1DecodeOk.carrier st)))
 (ub s1 : Slice U8) (v : alloc.vec.Vec U8)
 (tx1 : AspisR1CurrentCaller.verifier.candidate.tx1 (NNH_Run5bCurrentShape.current (NOC_Tx1Forward.M c)
   (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation) (NNV_PreparedAtHost.digest c)
   (AspisR1CurrentCaller.FirstComposition.toCurrentPublic (C.semanticPublic stmt)) ub s1 10#usize () none = ok (.Ok v)) :
 first_decoded (S c) sp ub s1 10#usize = ok (.Ok v) := by
 unfold first_decoded
 noc_stp rfl
 rw [NNH_Run5bCurrentInventory.adapter]
 unfold AspisS6CurrentFirstInstallation.current
 rw [spEq,stEq,AspisS6CurrentFirstInstallation.observer_none]
 have dg : AspisS6CurrentFirstInstallation.toDigest (SolanaDigest.Insts.Aspis_coreDigestDigest32 (S c)) =
  NNV_PreparedAtHost.digest c := rfl
 rw [dg,tx1]
 noc_stp rfl
 rfl

theorem body {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (pa pba cka : r1_pool_adapter.owned.OwnedAccount) (cb ub pb s0 s1 : Slice U8)
 (st : NNH_S1HostCodec.Statement) (nat : Array U8 688#usize)
 (sp : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (v : alloc.vec.Vec U8)
 (cmpT : (S c).op1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,10#u8]) = ok true)
 (len3 : Slice.len xs = 3#usize)
 (i0 : Slice.index_usize xs 0#usize = ok pa) (i1 : Slice.index_usize xs 1#usize = ok pba)
 (i2 : Slice.index_usize xs 2#usize = ok cka)
 (distRun : r1_pool_adapter.owned.require_distinct_accounts (S c) (Array.make 3#usize [pa,pba,cka]) = ok (.Ok ()))
 (rbP : r1_pool_adapter.owned.require_readonly_buffer pa = ok (.Ok ()))
 (rbU : r1_pool_adapter.owned.require_readonly_buffer pba = ok (.Ok ()))
 (ckOk : r1_pool_adapter.owned.require_verifier_checkpoint (S c) cka program true = ok (.Ok ()))
 (cbRun : r1_pool_adapter.owned.OwnedAccount.data (S c) cka = ok (.Ok cb))
 (zr : r1_pool_adapter.owned.require_zero cb = ok (.Ok ()))
 (ubRun : r1_pool_adapter.owned.OwnedAccount.data (S c) pba = ok (.Ok ub))
 (decRun : (S c).op47 ub = ok (.Ok st))
 (val21 : (S c).op21 st = ok (.Ok ()))
 (enc : ∃ cm, aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common st = ok cm ∧
   (S c).op24 cm.lane_transition.candidate_afterstate = ok (.Ok nat))
 (pbRun : r1_pool_adapter.owned.OwnedAccount.data (S c) pa = ok (.Ok pb))
 (pbytes : _root_.AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES = ok 57607#usize)
 (lenPb : Slice.len pb = 58295#usize)
 (s0Run : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) pb {«end» := 688#usize} = ok s0)
 (neRun : (S c).op0 core.cmp.PartialEqU8 s0 nat = ok false)
 (tag : Slice.index_usize pb 696#usize = ok 2#u8)
 (spRun : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public st = ok sp)
 (s1Run : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) pb ⟨688#usize,58295#usize⟩ = ok s1)
 (d1 : Slice.index_usize data 1#usize = ok 10#u8)
 (fd : first_decoded (S c) sp ub s1 10#usize = ok (.Ok v))
 (lenEq : alloc.vec.Vec.len v = Slice.len cb) :
 r1_pool_adapter.owned.stage1_owned (S c) program xs data = .ok (.Ok v) := by
 obtain ⟨cm,cmRun,enc24⟩ := enc
 have hck : lift (Usize.checked_add 688#usize 57607#usize) = ok (some 58295#usize) := by
  rw [NNH_Stage2Sizes.checkedEnd]; rfl
 have off : lift (Usize.wrapping_add 688#usize 8#usize) = ok 696#usize := by
  have e : Usize.wrapping_add 688#usize 8#usize = 696#usize := by
   apply UScalar.eq_of_val_eq
   have cap : (688#usize).val + (8#usize).val < UScalar.size .Usize := by rw [UScalar.size_def]; scalar_tac
   rw [Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt cap]
   scalar_tac
  rw [e]; rfl
 have cast : lift (UScalar.cast .Usize 10#u8) = ok 10#usize := by
  have e : UScalar.cast .Usize 10#u8 = 10#usize := by apply UScalar.eq_of_val_eq; scalar_tac
  rw [e]; rfl
 unfold r1_pool_adapter.owned.stage1_owned
 noc_stp cmpT
 s1n
 simp only [len3,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
 noc_stp i0
 noc_stp i1
 noc_stp i2
 noc_stp distRun
 s1n
 noc_stp rbP
 s1n
 noc_stp rbU
 s1n
 noc_stp ckOk
 s1n
 noc_stp cbRun
 s1n
 noc_stp zr
 s1n
 noc_stp ubRun
 s1n
 noc_stp decRun
 s1n
 noc_stp val21
 noc_stp rfl
 s1n
 noc_stp cmRun
 noc_stp enc24
 noc_stp rfl
 s1n
 noc_stp pbRun
 s1n
 noc_stp pbytes
 noc_stp (NNH_Stage2Sizes.afterstate (S c))
 noc_stp hck
 noc_stp rfl
 s1n
 simp only [lenPb,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
 noc_stp s0Run
 noc_stp neRun
 s1n
 noc_stp off
 noc_stp tag
 noc_stp rfl
 s1n
 noc_stp spRun
 noc_stp s1Run
 noc_stp d1
 noc_stp cast
 noc_stp fd
 s1n
 simp only [lenEq,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]

/-- The 345 Ok clause at the corrected host (NOT the A1 field): a returned
library 345 value is the model stage1_owned's Ok result with the SAME saved
bytes. No Root0, success, selector or representation premise. -/
theorem ok345 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (called : NNH_ReturnsBundle.tx1Value ⟨key program,accounts xs,bytes data⟩ (NOC_Run5bCtx.envOf c) =
  .ok (bytes saved.deref)) :
 r1_pool_adapter.owned.stage1_owned (S c) program xs data = .ok (.Ok saved) := by
 obtain ⟨p,pub,ck,shape,_,⟨packet⟩⟩ := NNH_Stage1TopCut.produce _ _ _ called
 have dataEq : bytes data = [3,10] := NNH_Tx1SuccessfulRoute.source _ _ _ called
 change accounts xs = [p,pub,ck] at shape
 obtain ⟨pa,i0,e0⟩ := NNH_AccountIndexOk.value xs 0#usize p (by rw [shape]; rfl)
 obtain ⟨pba,i1,e1⟩ := NNH_AccountIndexOk.value xs 1#usize pub (by rw [shape]; rfl)
 obtain ⟨cka,i2,e2⟩ := NNH_AccountIndexOk.value xs 2#usize ck (by rw [shape]; rfl)
 have len3 : Slice.len xs = 3#usize := by
  apply UScalar.eq_of_val_eq
  change xs.val.length = 3
  have l := congrArg List.length shape
  simp only [accounts,List.length_map] at l
  rw [l]; rfl
 have dist : RSL.distinctKeys ((Array.make 3#usize [pa,pba,cka]).val.map NNH_ModelCarrier.account) = true := by
  have d := packet.distinct
  unfold RSL.requireDistinct at d
  split at d
  · rename_i h
    show RSL.distinctKeys [account pa,account pba,account cka] = true
    rw [e0,e1,e2]; exact h
  · cases d
 obtain ⟨cb,cbRun,cbEq⟩ := NNH_CorrectTx2Inputs.getters (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c)
  c.fixed.indexError c.fixed.reservation cka packet.checkpoint_data
  ((congrArg RSL.OwnedAccount.bytes e2).trans packet.checkpoint_read)
 obtain ⟨ub,ubRun,ubEq⟩ := NNH_CorrectTx2Inputs.getters (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c)
  c.fixed.indexError c.fixed.reservation pba packet.public_data
  ((congrArg RSL.OwnedAccount.bytes e1).trans packet.public_read)
 obtain ⟨st,decRun,stEq⟩ := NNH_S1CodecOk.decode (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c)
  c.fixed.indexError c.fixed.reservation ub packet.statement ((congrArg C.decodeStatement ubEq).trans packet.decode)
 have val21 : (S c).op21 st = ok (.Ok ()) := by
  have slot : (S c).op21 st = NNH_S1HostCodec.validate st := rfl
  rw [slot]
  exact NNH_S1HostCodec.validate_ok st (by rw [stEq]; exact packet.valid)
 obtain ⟨cm,cmRun⟩ := commonOk st
 obtain ⟨nat,natRun,natEq⟩ := NNH_S1CodecOk.encode packet.statement packet.candidate packet.encode
 have enc := NNX_CommonEncode.source c st
 rw [cmRun,bind_tc_ok,stEq,natRun] at enc
 obtain ⟨pb,pbRun,pbEq⟩ := NNH_CorrectTx2Inputs.getters (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c)
  c.fixed.indexError c.fixed.reservation pa packet.proof_data
  ((congrArg RSL.OwnedAccount.bytes e0).trans packet.proof_read)
 have g := packet.proof_guard
 have gAB := (Bool.or_eq_false_iff.mp g).1
 obtain ⟨lenPb,⟨s0,s0Run,neRun⟩,tag⟩ := gateLemma c pb nat packet.proof_data packet.candidate pbEq
  (bne_eq_false_iff_eq.mp (Bool.or_eq_false_iff.mp gAB).1)
  (bne_eq_false_iff_eq.mp (Bool.or_eq_false_iff.mp gAB).2)
  (bne_eq_false_iff_eq.mp (Bool.or_eq_false_iff.mp g).2) natEq
 obtain ⟨sp,spRun,spEq⟩ := publicBinding st
 have pbLen : pb.val.length = 58295 := by
  have := congrArg UScalar.val lenPb; exact this
 obtain ⟨s1,s1Run,s1Same⟩ := NNH_SliceRangeOk.value pb 688#usize 58295#usize (by scalar_tac)
  (by change (58295#usize).val ≤ pb.val.length; rw [pbLen]; scalar_tac)
 have dv : data.val = [3#u8,10#u8] := by
  apply NNH_ByteListInjective.value
  show bytes data = _
  rw [dataEq]; with_unfolding_all rfl
 have d1 : Slice.index_usize data 1#usize = ok 10#u8 := by
  apply indexAt; show data.val[1]? = _; rw [dv]; rfl
 have child := mapVErrOk _ _ _ packet.child
 have width : s1.val.length = 57607 := by
  have l := congrArg List.length s1Same
  rw [bytes_length] at l
  rw [l]
  have ext := NNH_Stage1ProofDomain.extent _ _ _ _ _ _ packet
  rw [← pbEq] at ext
  exact ext
 obtain ⟨v,tx1Run,vEq⟩ := NOC_Tx1Forward.source c _ ub s1 10#usize ubEq.symm
  (by show RSL.slice packet.proof_data RSL.AFTERSTATE_BYTES RSL.PROOF_ACCOUNT_BYTES = bytes s1
      rw [s1Same,← pbEq]; rfl)
  (by show ((bytes data).getD 1 0).toNat = (10#usize).val
      rw [dataEq]; rfl)
  width _ child
 have vs : v = saved := vecEq _ _ vEq
 subst vs
 have fd := fdLemma c st packet.statement stEq sp spEq ub s1 v tx1Run
 have lenEq : alloc.vec.Vec.len v = Slice.len cb := by
  apply UScalar.eq_of_val_eq
  change v.val.length = cb.val.length
  have l1 := packet.saved_length
  rw [← cbEq] at l1
  simp only [bytes_length] at l1
  exact l1
 exact body c program xs data pa pba cka cb ub pb s0 s1 st nat sp v
  (cmpLemma c data dataEq) len3 i0 i1 i2
  (NNH_AuthSdkDistinct.value (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c) c.fixed.indexError
    c.fixed.reservation (Array.make 3#usize [pa,pba,cka]) (by decide) dist)
  (rbLemma pa p e0 packet.proof_readonly) (rbLemma pba pub e1 packet.public_readonly)
  (ckLemma c cka ck program e2 packet.checkpoint_owned) cbRun
  (NNH_Stage1ZeroCurrent.source cb (by rw [cbEq]; exact packet.checkpoint_zero))
  ubRun decRun val21 ⟨cm,cmRun,enc⟩ pbRun
  (by unfold _root_.AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES; exact proofBytes)
  lenPb s0Run neRun tag spRun s1Run d1 fd lenEq
#print axioms proofBytes
#print axioms publicBinding
#print axioms commonOk
#print axioms neFalse
#print axioms prefixRead
#print axioms indexAt
#print axioms vecEq
#print axioms mapVErrOk
#print axioms byteSame
#print axioms cmpLemma
#print axioms ckLemma
#print axioms rbLemma
#print axioms gateLemma
#print axioms fdLemma
#print axioms body
#print axioms ok345
end NOC_Stage1Forward
end
