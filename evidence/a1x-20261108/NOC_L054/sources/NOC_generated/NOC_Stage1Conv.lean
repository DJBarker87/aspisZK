import NOC_Stage1Inv
import RPz7_S6CurrentCodecTotalV1
set_option autoImplicit false
noncomputable section
namespace NOC_Stage1Conv
open Aeneas Aeneas.Std Result AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries AspisR1.NOC_FinishSource
open NOC_Stage1Inv (S Facts outerOk keyInj distinct3 neConv consume)

/-- Route compare: an Ok-true native compare fixes the instruction data. -/
theorem routeData {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (data : Slice U8) (tag : U8)
 (h : (S c).op1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,tag]) = ok true) :
 bytes data = [3,byte tag] ∧ data.val = [3#u8,tag] := by
 have cmp := NNH_Tx1RouteCompare.source (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c) c.fixed.indexError
  c.fixed.reservation data tag
 have e := Result.ok.inj (h.symm.trans cmp)
 have d : bytes data = [3,byte tag] := of_decide_eq_true e.symm
 refine ⟨d,?_⟩
 apply NNH_ByteListInjective.value
 show bytes data = _
 rw [d]; with_unfolding_all rfl

theorem kOf {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (F : Facts c program xs data saved) (tag : U8) (dv : data.val = [3#u8,tag]) :
 F.kk = UScalar.cast .Usize tag := by
 have d1 : Slice.index_usize data 1#usize = ok tag := by
  apply NOC_Stage1Forward.indexAt; show data.val[1]? = _; rw [dv]; rfl
 have e1 : F.d1v = tag := Result.ok.inj (F.hd1.symm.trans d1)
 have hkk := F.hkk
 rw [e1] at hkk
 exact Result.ok.inj (hkk.symm.trans rfl)

/-- Account shape from the SAME native index replies. -/
theorem shapeOf {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (F : Facts c program xs data saved) :
 accounts xs = [account F.pa,account F.pba,account F.cka] := by
 have hl' : Slice.len xs = 3#usize := bne_eq_false_iff_eq.mp F.hl
 have hlen3 : xs.val.length = 3 := by have := congrArg UScalar.val hl'; exact this
 obtain ⟨x0,x1,x2,hx⟩ := NNH_ThreeAccounts.shape xs.val hlen3
 have shape0 : accounts xs = [account x0,account x1,account x2] := by
  show xs.val.map account = _; rw [hx]; rfl
 obtain ⟨n0,j0,f0⟩ := NNH_AccountIndexOk.value xs 0#usize (account x0) (by rw [shape0]; rfl)
 obtain ⟨n1,j1,f1⟩ := NNH_AccountIndexOk.value xs 1#usize (account x1) (by rw [shape0]; rfl)
 obtain ⟨n2,j2,f2⟩ := NNH_AccountIndexOk.value xs 2#usize (account x2) (by rw [shape0]; rfl)
 have q0 : n0 = F.pa := Result.ok.inj (j0.symm.trans F.i0)
 have q1 : n1 = F.pba := Result.ok.inj (j1.symm.trans F.i1)
 have q2 : n2 = F.cka := Result.ok.inj (j2.symm.trans F.i2)
 rw [shape0,← f0,← f1,← f2,q0,q1,q2]

/-- The second accepted route (data [3,11]) reaches first_decoded at split 11,
whose installed current tx1 returns the Parse error: never Ok. -/
theorem fd11 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx)
 (sp : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public) (ub s1 : Slice U8)
 (k : Usize) (hk : k.val = 11) (v : alloc.vec.Vec U8) :
 first_decoded (S c) sp ub s1 k ≠ ok (.Ok v) := by
 intro h
 have k11 : k = 11#usize := UScalar.eq_of_val_eq (by rw [hk]; rfl)
 subst k11
 unfold first_decoded at h
 ncj_br h
 rw [NNH_Run5bCurrentInventory.adapter] at h
 unfold AspisS6CurrentFirstInstallation.current at h
 obtain ⟨x | _, htx, hk2⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill hk2
 unfold AspisR1CurrentCaller.verifier.candidate.tx1 at htx
 have ks : ((11#usize : Usize) != AspisR1CurrentCaller.compact.SPLIT) = true := by
  first | (unfold AspisR1CurrentCaller.compact.SPLIT; decide) | rfl | (unfold AspisR1CurrentCaller.compact.SPLIT; simp) | decide
 rw [ks] at htx
 nci_kill htx

/-- Authentication guards: distinct keys, read-only buffers, checkpoint,
getters and zero checkpoint, at the library carriers. -/
theorem guards {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (F : Facts c program xs data saved) :
 RSL.requireDistinct [account F.pa,account F.pba,account F.cka] = .ok () ∧
 RSL.readonlyBuffer (account F.pa) = .ok () ∧ RSL.readonlyBuffer (account F.pba) = .ok () ∧
 NNH_ReturnedClone.checkpointValue (account F.cka) (key program) true = .ok () ∧
 (account F.cka).bytes = .ok (bytes F.cb) ∧ RSL.requireZero (bytes F.cb) = .ok () ∧
 (account F.pba).bytes = .ok (bytes F.ub) ∧ (account F.pa).bytes = .ok (bytes F.pb) := by
 have nat0 := NGL_DistinctInduction.source (NNH_Tx2Configuration.sdk (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c)
  c.fixed.indexError c.fixed.reservation) (Array.make 3#usize [F.pa,F.pba,F.cka]) (by decide)
 rw [NNH_Tx2Configuration.readonly] at nat0
 obtain ⟨d01,d02,d12⟩ := distinct3 F.pa F.pba F.cka (nat0.symm.trans F.hdist)
 have k01 : (account F.pba).key ≠ (account F.pa).key := fun e => d01 (keyInj _ _ e).symm
 have k02 : (account F.cka).key ≠ (account F.pa).key := fun e => d02 (keyInj _ _ e).symm
 have k12 : (account F.cka).key ≠ (account F.pba).key := fun e => d12 (keyInj _ _ e).symm
 have dk : RSL.distinctKeys [account F.pa,account F.pba,account F.cka] = true := by
  simp [RSL.distinctKeys,k01,k02,k12]
 have distinctL : RSL.requireDistinct [account F.pa,account F.pba,account F.cka] = .ok () := by
  unfold RSL.requireDistinct; rw [dk] <;> rfl
 have rbP : RSL.readonlyBuffer (account F.pa) = .ok () :=
  (outerOk _ _ _ _ F.hrbP (NNH_AuthGuardPorts.buffer F.pa)).symm
 have rbU : RSL.readonlyBuffer (account F.pba) = .ok () :=
  (outerOk _ _ _ _ F.hrbU (NNH_AuthGuardPorts.buffer F.pba)).symm
 have ckm := NNH_ModelCheckpoint.value
  (NNH_MRegistryOps.install (NNH_LaneModel.install (S c)) LIB_Deployed.deployed (NNH_HostCtx.envOf c)) F.cka program true
 have ckc := NNH_AuthGuardCongr.checkpoint (S c) (NGL_CheckpointModel.install
    (NNH_MRegistryOps.install (NNH_LaneModel.install (S c)) LIB_Deployed.deployed (NNH_HostCtx.envOf c)))
    (by rfl) (by rfl) (by rfl) F.cka program true
 have ckV : NNH_ReturnedClone.checkpointValue (account F.cka) (key program) true = .ok () :=
  (outerOk _ _ _ _ (ckc.symm.trans F.hck) ckm).symm
 have gcb : NNH_ModelCarrier.outer _ (r1_pool_adapter.owned.OwnedAccount.data (S c) F.cka) = ok (account F.cka).bytes :=
  NNH_ModelCarrier.getter (S c) F.cka
 have gub : NNH_ModelCarrier.outer _ (r1_pool_adapter.owned.OwnedAccount.data (S c) F.pba) = ok (account F.pba).bytes :=
  NNH_ModelCarrier.getter (S c) F.pba
 have gpb : NNH_ModelCarrier.outer _ (r1_pool_adapter.owned.OwnedAccount.data (S c) F.pa) = ok (account F.pa).bytes :=
  NNH_ModelCarrier.getter (S c) F.pa
 exact ⟨distinctL,rbP,rbU,ckV,(outerOk _ _ _ _ F.hcb gcb).symm,
  (outerOk _ _ _ _ F.hz (NNH_Stage1ZeroCurrent.projection F.cb)).symm,
  (outerOk _ _ _ _ F.hub gub).symm,(outerOk _ _ _ _ F.hpb gpb).symm⟩

/-- Statement codec facts: decode, validate (with the validated public digest)
and candidate encode, at the SAME statement carrier. -/
theorem codec {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (F : Facts c program xs data saved) :
 C.decodeStatement (LIB_Carriers.bytes F.ub) = some (NNH_S1DecodeOk.carrier F.st) ∧
 C.validateStatement (NNH_S1DecodeOk.carrier F.st) = true ∧
 LIB_VPublicDomain.publicDigestDom (C.semanticPublic (NNH_S1DecodeOk.carrier F.st)) ∧
 C.encodeCandidate (NNH_S1DecodeOk.carrier F.st) = some (F.nat.val.map NMT_345.byte) := by
 have hdec' : AspisS6CurrentCodecInstallation.decode F.ub = ok (.Ok F.st) := F.hdec
 obtain ⟨enc, _, encv⟩ := AspisS6CurrentCodecInstallation.accepted_inverse F.ub F.st hdec'
 have ubLen : (LIB_Carriers.bytes F.ub).length = 1880 := by
  rw [NOC_PrepareFront.bytes_length, ← encv]
  first | exact enc.property | (have := enc.property; scalar_tac) | simp
 have decL : C.decodeStatement (LIB_Carriers.bytes F.ub) = some (NNH_S1DecodeOk.carrier F.st) := by
  change LIBC_S1.decode (LIB_Carriers.bytes F.ub) = _
  unfold LIBC_S1.decode
  rw [dif_pos ubLen, LIBC_Bytes.from_native]
  unfold NMT_345.decodeCall
  rw [hdec']
  all_goals first | rfl | (simp only [NMT_345.mapOuter,NMT_345.mapCore]; done) | (simp [NMT_345.mapOuter,NMT_345.mapCore])
 have v21 : NNH_S1HostCodec.validate F.st = .ok (.Ok ()) := F.h21
 have vn := NOM_TerminalDomain.validate_native F.st v21
 have validL : C.validateStatement (NNH_S1DecodeOk.carrier F.st) = true := (LIBC_S1.valid_iff _).mpr vn
 obtain ⟨cm, hcm, h24⟩ := F.enc
 have enc0 := NNX_CommonEncode.source c F.st
 rw [hcm, bind_tc_ok] at enc0
 have enc2 := enc0.symm.trans h24
 have encCall : NMT_345.encodeCall (NMT_345.commonValue (NNH_S1DecodeOk.carrier F.st)).lane_transition.candidate_afterstate =
   .ok (.Ok F.nat) := by
  revert enc2
  cases hE : NMT_345.encodeCall (NMT_345.commonValue (NNH_S1DecodeOk.carrier F.st)).lane_transition.candidate_afterstate with
  | ok r => cases r with
   | Ok o => intro e; first | (cases e; rfl) | (simp only at e; rw [e]) | simp_all
   | Err _ => intro e; first | (cases e; done) | simp at e
  | fail _ => intro e; first | (cases e; done) | simp at e
  | div => intro e; first | (cases e; done) | simp at e
 have encL : C.encodeCandidate (NNH_S1DecodeOk.carrier F.st) = some (F.nat.val.map NMT_345.byte) := by
  change LIBC_S1.encode _ = _
  unfold LIBC_S1.encode
  rw [encCall] <;> rfl
 exact ⟨decL,validL,NOM_TerminalDomain.validated_digest F.st v21,encL⟩

/-- The proof-account gate at the library carriers. -/
theorem gate {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (F : Facts c program xs data saved) :
 F.pb.val.length = 58295 ∧
 ((bytes F.pb).length != 58295 || (bytes F.pb).take 688 != F.nat.val.map NMT_345.byte ||
   (bytes F.pb).getD 696 0 != (2 : UInt8)) = false := by
 have hlen' : Slice.len F.pb = 58295#usize := bne_eq_false_iff_eq.mp F.hlen
 have pbLen : F.pb.val.length = 58295 := by have := congrArg UScalar.val hlen'; exact this
 obtain ⟨pre,preRun,preVal⟩ := NOC_Stage1Forward.prefixRead F.pb 688#usize
  (by change (688#usize).val ≤ F.pb.val.length; rw [pbLen]; scalar_tac)
 have es0 : F.s0 = pre := Result.ok.inj (F.hs0.symm.trans preRun)
 have hne' : core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8 F.s0 (Array.to_slice F.nat) = ok false := F.hne
 have snat := neConv _ _ hne'
 have takeEq : (bytes F.pb).take 688 = F.nat.val.map NMT_345.byte := by
  have nb : F.nat.val.map NMT_345.byte = F.nat.val.map byte :=
   List.map_congr_left (fun x _ => NOC_Stage1Forward.byteSame x)
  rw [nb]
  have sv : F.pb.val.slice 0 688 = F.nat.val := by
   have := congrArg Subtype.val snat
   rw [es0, preVal] at this
   exact this
  rw [← sv]
  show List.take 688 (List.map byte F.pb.val) = List.map byte (List.slice 0 688 F.pb.val)
  first
   | (simp only [List.slice,List.map_take,List.drop_zero,Nat.sub_zero])
   | (simp [List.slice,List.map_take])
   | rfl
 have tagL : (bytes F.pb).getD 696 0 = 2 := by
  have inside : 696 < F.pb.val.length := by rw [pbLen]; decide
  obtain ⟨out,run,value⟩ := NNH_ResultWp.expose _ _ (Slice.index_usize_spec F.pb 696#usize inside)
  have et : F.t = out := Result.ok.inj (F.htag.symm.trans run)
  have t2 : F.t = 2#u8 := bne_eq_false_iff_eq.mp F.htv
  show (F.pb.val.map byte).getD 696 0 = 2
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem inside]
  simp only [Option.map_some, Option.getD_some]
  have h696 : F.pb.val[696] = out := by rw [value] <;> rfl
  rw [h696, ← et, t2]
  with_unfolding_all rfl
 have pbBytesLen : (bytes F.pb).length = 58295 := by
  rw [bytes_length]; exact pbLen
 refine ⟨pbLen,?_⟩
 rw [pbBytesLen, takeEq, tagL]; simp

/-- The 094 child: first_decoded inverted to the installed current tx1, then
NOC_Tx1Conv.tx1 and the forward determinism of NOC_Tx1Forward.source. -/
theorem child {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (F : Facts c program xs data saved) (dataEq : bytes data = [3,10]) (ek : F.kk = 10#usize)
 (pbLen : F.pb.val.length = 58295)
 (digest : LIB_VPublicDomain.publicDigestDom (C.semanticPublic (NNH_S1DecodeOk.carrier F.st))) :
 NNH_Tx1ReturnedValues.mapVErrValue VL (NNH_Tx1Returns.values.tx1
   ⟨C.semanticPublic (NNH_S1DecodeOk.carrier F.st),bytes F.ub,
    RSL.slice (bytes F.pb) RSL.AFTERSTATE_BYTES RSL.PROOF_ACCOUNT_BYTES,((bytes data).getD 1 0).toNat⟩
   (NOC_Run5bCtx.envOf c)) = .ok (bytes saved.deref) := by
 obtain ⟨sp', hsp', spEq⟩ := NOC_Stage1Forward.publicBinding F.st
 have esp : F.sp = sp' := Result.ok.inj (F.hsp.symm.trans hsp')
 have hfd := F.hfd
 rw [ek, esp] at hfd
 have fd2 := hfd
 unfold first_decoded at fd2
 ncj_br fd2
 rw [NNH_Run5bCurrentInventory.adapter] at fd2
 unfold AspisS6CurrentFirstInstallation.current at fd2
 rw [spEq,AspisS6CurrentFirstInstallation.observer_none] at fd2
 have dg : AspisS6CurrentFirstInstallation.toDigest (SolanaDigest.Insts.Aspis_coreDigestDigest32 (S c)) =
  NNV_PreparedAtHost.digest c := rfl
 rw [dg] at fd2
 obtain ⟨x | _, htx0, fdk⟩ := NOC_SemConv.bindInv fd2; rotate_left; nci_kill fdk
 unfold AspisS6OuterNativeOps.resultMap at htx0
 obtain ⟨y | _, htx, hk⟩ := NOC_SemConv.bindInv htx0; rotate_left; nci_kill hk
 obtain ⟨s1',s1Run,s1Same⟩ := NNH_SliceRangeOk.value F.pb 688#usize 58295#usize (by scalar_tac)
  (by change (58295#usize).val ≤ F.pb.val.length; rw [pbLen]; scalar_tac)
 have es1 : F.s1 = s1' := Result.ok.inj (F.hs1.symm.trans s1Run)
 rw [← es1] at s1Same
 have width : F.s1.val.length = 57607 := by
  have l := congrArg List.length s1Same
  rw [bytes_length] at l
  rw [l]
  simp only [RSL.slice,List.length_take,List.length_drop,bytes_length,pbLen]
  all_goals first | rfl | decide | omega | scalar_tac | simp
 have hproof : RSL.slice (bytes F.pb) RSL.AFTERSTATE_BYTES RSL.PROOF_ACCOUNT_BYTES = bytes F.s1 := by
  rw [s1Same] <;> rfl
 have hk10 : ((bytes data).getD 1 0).toNat = 10 := by rw [dataEq]; rfl
 obtain ⟨out, hout⟩ := NOC_Tx1Conv.tx1 c
  ⟨C.semanticPublic (NNH_S1DecodeOk.carrier F.st),bytes F.ub,
   RSL.slice (bytes F.pb) RSL.AFTERSTATE_BYTES RSL.PROOF_ACCOUNT_BYTES,((bytes data).getD 1 0).toNat⟩
  F.ub F.s1 hproof hk10 width digest ⟨y, htx⟩
 obtain ⟨v',tx1Run,vEq⟩ := NOC_Tx1Forward.source c _ F.ub F.s1 10#usize rfl hproof hk10 width _ hout
 have fwdFd := NOC_Stage1Forward.fdLemma c F.st (NNH_S1DecodeOk.carrier F.st) rfl sp' spEq F.ub F.s1 v' tx1Run
 have evv : saved = v' := core.result.Result.Ok.inj (Result.ok.inj (hfd.symm.trans fwdFd))
 subst evv
 change NNH_Tx1ReturnedValues.mapVErrValue VL (NNH_Tx1Returns.value _ (NOC_Run5bCtx.envOf c)) = _
 rw [hout, ← vEq] <;> rfl

/-- 345 converse at the corrected host: an Ok model stage1_owned is a returned
library 345 value with the SAME saved bytes. With NOC_Stage1Forward.ok345 this
is the Ok-iff; its contraposition is the weak-Err clause. -/
theorem conv {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (called : r1_pool_adapter.owned.stage1_owned (S c) program xs data = .ok (.Ok saved)) :
 NNH_ReturnsBundle.tx1Value ⟨key program,accounts xs,bytes data⟩ (NOC_Run5bCtx.envOf c) =
  .ok (bytes saved.deref) := by
 obtain ⟨F⟩ := NOC_Stage1Inv.invert c program xs data saved called
 have shape := shapeOf c program xs data saved F
 obtain ⟨dataEq,ek⟩ : bytes data = [3,10] ∧ F.kk = 10#usize := by
  rcases F.hcmp with h10 | h11
  · obtain ⟨d,dv⟩ := routeData c data 10#u8 h10
    have byte10 : byte 10#u8 = 10 := by with_unfolding_all rfl
    rw [byte10] at d
    have cast : UScalar.cast .Usize 10#u8 = 10#usize := by apply UScalar.eq_of_val_eq; scalar_tac
    exact ⟨d, (kOf c program xs data saved F 10#u8 dv).trans cast⟩
  · obtain ⟨_,dv⟩ := routeData c data 11#u8 h11
    have cast : UScalar.cast .Usize 11#u8 = 11#usize := by apply UScalar.eq_of_val_eq; scalar_tac
    have k11 : F.kk = 11#usize := (kOf c program xs data saved F 11#u8 dv).trans cast
    exact absurd F.hfd (fd11 c F.sp F.ub F.s1 F.kk (by rw [k11]; rfl) saved)
 obtain ⟨distinctL,rbP,rbU,ckV,ckRead,zV,ubRead,pbRead⟩ := guards c program xs data saved F
 obtain ⟨decL,validL,digest,encL⟩ := codec c program xs data saved F
 obtain ⟨pbLen,guard⟩ := gate c program xs data saved F
 have childL := child c program xs data saved F dataEq ek pbLen digest
 have hsv' : alloc.vec.Vec.len saved = Slice.len F.cb := bne_eq_false_iff_eq.mp F.hsv
 have savedLen : (bytes saved.deref).length = (bytes F.cb).length := by
  have := congrArg UScalar.val hsv'
  simp only [bytes_length]
  exact this
 have len3acc : (accounts xs).length = 3 := by rw [shape]; rfl
 have routeF : RSL.TX1_345.badRoute ⟨key program,[account F.pa,account F.pba,account F.cka],bytes data⟩ = false := by
  simp [RSL.TX1_345.badRoute,dataEq]
 have pk : NNH_Stage1Cut.Packet ⟨key program,accounts xs,bytes data⟩ (account F.pa) (account F.pba) (account F.cka)
   (bytes saved.deref) (NOC_Run5bCtx.envOf c) :=
  ⟨distinctL,rbP,rbU,ckV,bytes F.cb,ckRead,zV,bytes F.ub,ubRead,NNH_S1DecodeOk.carrier F.st,decL,validL,
   F.nat.val.map NMT_345.byte,encL,bytes F.pb,pbRead,guard,childL,savedLen⟩
 show NNH_Stage1RefEval.value VL P NNH_Tx1Returns.values C _ _ = _
 simp only [NNH_Stage1RefEval.value,routeF,shape,if_false,Bool.false_eq_true,↓reduceIte]
 exact consume _ _ _ _ _ _ pk

#print axioms routeData
#print axioms kOf
#print axioms shapeOf
#print axioms fd11
#print axioms guards
#print axioms codec
#print axioms gate
#print axioms child
#print axioms conv
end NOC_Stage1Conv
end
