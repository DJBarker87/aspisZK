import NOC_Tx1Conv
import NOC_Stage1Forward
import S6CurrentCodecTotalV1
set_option autoImplicit false
noncomputable section
namespace NOC_Stage1Conv
open Aeneas Aeneas.Std Result AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier NNH_Libraries AspisR1.NOC_FinishSource

abbrev S {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := NOC_Stage1Forward.S c

/-- A native carrier projection of an Ok reply. -/
theorem outerOk {A B : Type} (f : A → B) (r : Result A) (a : A) (b : B) (hr : r = ok a)
 (h : NNH_ModelCarrier.outer f r = ok b) : f a = b := by
 subst hr; exact Result.ok.inj h

theorem keyInj (a b : Array U8 32#usize) (h : NND_Carrier.key a = NND_Carrier.key b) : a = b := by
 have e := congrArg NND_Carrier.unkey h
 simpa only [NND_Carrier.key_back] using e

theorem wadd (a b z : Usize) (h : a.val + b.val = z.val) (cap : a.val + b.val < UScalar.size .Usize) :
 Usize.wrapping_add a b = z := by
 apply UScalar.eq_of_val_eq
 rw [Usize.wrapping_add_val_eq, Nat.mod_eq_of_lt cap]
 exact h

/-- Converse of the distinct guard on three accounts: an Ok native scan has
pairwise distinct keys. -/
theorem distinct3 (pa pb pc : r1_pool_adapter.owned.OwnedAccount)
 (h : NGL_DistinctInduction.reference (Array.make 3#usize [pa,pb,pc]) = ok (.Ok ())) :
 pa.key ≠ pb.key ∧ pa.key ≠ pc.key ∧ pb.key ≠ pc.key := by
 have a0 : Usize.wrapping_add 0#usize 1#usize = 1#usize :=
  wadd _ _ _ (by scalar_tac) (by rw [UScalar.size_def]; scalar_tac)
 have a1 : Usize.wrapping_add 1#usize 1#usize = 2#usize :=
  wadd _ _ _ (by scalar_tac) (by rw [UScalar.size_def]; scalar_tac)
 have a2 : Usize.wrapping_add 2#usize 1#usize = 3#usize :=
  wadd _ _ _ (by scalar_tac) (by rw [UScalar.size_def]; scalar_tac)
 refine ⟨?_,?_,?_⟩ <;> intro e <;>
  simp [NGL_DistinctInduction.reference,NGL_DistinctInduction.outer,NGL_DistinctInduction.inner,
   NGL_DistinctInduction.keyAt,a0,a1,a2,e] at h

/-- Slice inequality converse. -/
theorem neConv (s t : Slice U8) (h : core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8 s t = ok false) :
 s = t := by
 have spec := core.slice.cmp.PartialEqSlice.ne_homo_spec core.cmp.PartialEqU8 s t (by
  intro x y
  first
   | (simp [core.cmp.PartialEqU8])
   | (unfold core.cmp.PartialEqU8; simp)
   | (simp [core.cmp.PartialEqU8, bne_iff_ne]))
 obtain ⟨b,run,hb⟩ := NNH_ResultWp.expose _ _ spec
 rw [run] at h
 have bf : b = false := Result.ok.inj h
 subst bf
 refine Classical.byContradiction (fun hne => ?_)
 have t := hb.mpr hne
 cases t

theorem esStep {α : Type} {x : Except RSL.ProgramError Unit} {y : Except RSL.ProgramError α}
 (hx : x = .ok ()) : NND_Returned.eseq x y = y := by subst hx; rfl
theorem ebStep {α β : Type} {x : Except RSL.ProgramError α} {a : α} {k : α → Except RSL.ProgramError β}
 (hx : x = .ok a) : NND_Returned.ebind x k = k a := by subst hx; rfl
theorem optOk {α : Type} {x : Option α} {a : α} {e : RSL.ProgramError} (hx : x = some a) :
 NND_Returned.option x e = .ok a := by subst hx; rfl
theorem echeckOk {b : Bool} {e : RSL.ProgramError} (hb : b = false) : NND_Returned.echeck b e = .ok () := by
 subst hb; rfl

/-- Library consume: the SAME 345 packet is the body value. -/
theorem consume (a : RSL.TX1_345.Args) (p pub ck : RSL.OwnedAccount) (saved : RSL.Bytes) (env : RSL.Env)
 (pk : NNH_Stage1Cut.Packet a p pub ck saved env) :
 NNH_Stage1Eval.bodyValue VL P NNH_Tx1Returns.values C a p pub ck env = .ok saved := by
 unfold NNH_Stage1Eval.bodyValue
 refine (esStep pk.distinct).trans ?_
 refine (esStep pk.proof_readonly).trans ?_
 refine (esStep pk.public_readonly).trans ?_
 refine (esStep pk.checkpoint_owned).trans ?_
 refine (ebStep pk.checkpoint_read).trans ?_
 refine (esStep pk.checkpoint_zero).trans ?_
 refine (ebStep pk.public_read).trans ?_
 refine (esStep rfl).trans ?_
 refine (ebStep (optOk pk.decode)).trans ?_
 refine (esStep rfl).trans ?_
 refine (esStep (echeckOk (by simp [pk.valid]))).trans ?_
 refine (ebStep (optOk pk.encode)).trans ?_
 refine (ebStep pk.proof_read).trans ?_
 refine (esStep (echeckOk pk.proof_guard)).trans ?_
 refine (ebStep pk.child).trans ?_
 refine (esStep (echeckOk (by simp [pk.saved_length]))).trans ?_
 rfl

/-- 345 converse at the corrected host: an Ok model stage1_owned is a returned
library 345 value with the SAME saved bytes. With NOC_Stage1Forward.ok345 this
is the Ok-iff; its contraposition is the weak-Err clause. -/
theorem conv {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (called : r1_pool_adapter.owned.stage1_owned (S c) program xs data = .ok (.Ok saved)) :
 NNH_ReturnsBundle.tx1Value ⟨key program,accounts xs,bytes data⟩ (NOC_Run5bCtx.envOf c) =
  .ok (bytes saved.deref) := by
 have h := called
 unfold r1_pool_adapter.owned.stage1_owned at h
 -- route compare
 obtain ⟨b, hcmp, h⟩ := NOC_SemConv.bindInv h
 cases b
 · nci_kill h
 ncj_nrh h
 -- account count
 split at h
 · nci_kill h
 rename_i hl
 obtain ⟨pa, i0, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨pba, i1, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨cka, i2, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨u0 | _, hdist, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 obtain ⟨u1 | _, hrbP, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 obtain ⟨u2 | _, hrbU, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 obtain ⟨u3 | _, hck, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 obtain ⟨cb | _, hcb, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 obtain ⟨u5 | _, hz, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 obtain ⟨ub | _, hub, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 obtain ⟨st | _, hdec, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 obtain ⟨u21 | _, h21, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 ncj_br h
 obtain ⟨cm, hcm, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨nat | _, h24, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 ncj_br h
 obtain ⟨pb | _, hpb, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 have pbytes : _root_.AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES = ok 57607#usize := by
  unfold _root_.AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES; exact NOC_Stage1Forward.proofBytes
 ncj_step h pbytes
 ncj_step h (NNH_Stage2Sizes.afterstate (S c))
 have hckd : lift (Usize.checked_add 688#usize 57607#usize) = ok (some 58295#usize) := by
  rw [NNH_Stage2Sizes.checkedEnd]; rfl
 ncj_step h hckd
 ncj_br h
 ncj_br h
 -- proof length
 split at h
 · nci_kill h
 rename_i hlen
 obtain ⟨s0, hs0, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨b1, hne, h⟩ := NOC_SemConv.bindInv h
 cases b1
 rotate_left; nci_kill h
 ncj_nrh h
 have off : lift (Usize.wrapping_add 688#usize 8#usize) = ok 696#usize := by
  have e : Usize.wrapping_add 688#usize 8#usize = 696#usize :=
   wadd _ _ _ (by scalar_tac) (by rw [UScalar.size_def]; scalar_tac)
  rw [e]; rfl
 ncj_step h off
 obtain ⟨t, htag, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨tg, htg, h⟩ := NOC_SemConv.bindInv h
 cases htg
 ncj_nrh h
 split at h
 · nci_kill h
 rename_i htv
 obtain ⟨sp, hsp, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨s1, hs1, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨d1v, hd1, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨kk, hkk, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨v | _, hfd, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 ncj_br h
 split at h
 · nci_kill h
 rename_i hsv
 have vs : v = saved := core.result.Result.Ok.inj (Result.ok.inj h)
 subst vs
 -- route facts
 have cmp := NNH_Tx1RouteCompare.source (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c) c.fixed.indexError
  c.fixed.reservation data 10#u8
 have byte10 : byte 10#u8 = 10 := by with_unfolding_all rfl
 have dataEq : bytes data = [3,10] := by
  have e := Result.ok.inj (hcmp.symm.trans cmp)
  have d := of_decide_eq_true e.symm
  rw [byte10] at d; exact d
 have dv : data.val = [3#u8,10#u8] := by
  apply NNH_ByteListInjective.value
  show bytes data = _
  rw [dataEq]; with_unfolding_all rfl
 have d1 : Slice.index_usize data 1#usize = ok 10#u8 := by
  apply NOC_Stage1Forward.indexAt; show data.val[1]? = _; rw [dv]; rfl
 have e1 : d1v = 10#u8 := Result.ok.inj (hd1.symm.trans d1)
 subst e1
 have cast : lift (UScalar.cast .Usize 10#u8) = ok 10#usize := by
  have e : UScalar.cast .Usize 10#u8 = 10#usize := by apply UScalar.eq_of_val_eq; scalar_tac
  rw [e]; rfl
 have ek : kk = 10#usize := Result.ok.inj (hkk.symm.trans cast)
 subst ek
 -- accounts
 have hl' : Slice.len xs = 3#usize := by
  first
   | (simpa [bne_iff_ne] using hl)
   | (by_cases e : Slice.len xs = 3#usize
      · exact e
      · exact absurd (by simp [e]) hl)
 have hlen3 : xs.val.length = 3 := by have := congrArg UScalar.val hl'; exact this
 obtain ⟨x0,x1,x2,hx⟩ := NNH_ThreeAccounts.shape xs.val hlen3
 have shape0 : accounts xs = [account x0,account x1,account x2] := by
  show xs.val.map account = _; rw [hx]; rfl
 obtain ⟨n0,j0,f0⟩ := NNH_AccountIndexOk.value xs 0#usize (account x0) (by rw [shape0]; rfl)
 obtain ⟨n1,j1,f1⟩ := NNH_AccountIndexOk.value xs 1#usize (account x1) (by rw [shape0]; rfl)
 obtain ⟨n2,j2,f2⟩ := NNH_AccountIndexOk.value xs 2#usize (account x2) (by rw [shape0]; rfl)
 have q0 : n0 = pa := Result.ok.inj (j0.symm.trans i0)
 have q1 : n1 = pba := Result.ok.inj (j1.symm.trans i1)
 have q2 : n2 = cka := Result.ok.inj (j2.symm.trans i2)
 subst q0; subst q1; subst q2
 have shape : accounts xs = [account n0,account n1,account n2] := by rw [shape0,f0,f1,f2]
 have len3acc : (accounts xs).length = 3 := by rw [shape]; rfl
 have route : RSL.TX1_345.badRoute ⟨key program,accounts xs,bytes data⟩ = false := by
  simp [RSL.TX1_345.badRoute,dataEq,len3acc]
 -- distinct
 have nat0 := NGL_DistinctInduction.source (NNH_Tx2Configuration.sdk (NOC_Tx1Forward.M c) (NNH_HostCtx.envOf c)
  c.fixed.indexError c.fixed.reservation) (Array.make 3#usize [n0,n1,n2]) (by decide)
 rw [NNH_Tx2Configuration.readonly] at nat0
 cases u0
 obtain ⟨d01,d02,d12⟩ := distinct3 n0 n1 n2 (nat0.symm.trans hdist)
 have k01 : (account n1).key ≠ (account n0).key := fun e => d01 (keyInj _ _ e).symm
 have k02 : (account n2).key ≠ (account n0).key := fun e => d02 (keyInj _ _ e).symm
 have k12 : (account n2).key ≠ (account n1).key := fun e => d12 (keyInj _ _ e).symm
 have dk : RSL.distinctKeys [account n0,account n1,account n2] = true := by
  simp [RSL.distinctKeys,k01,k02,k12]
 have distinctL : RSL.requireDistinct [account n0,account n1,account n2] = .ok () := by
  unfold RSL.requireDistinct; rw [dk] <;> rfl
 -- read-only buffers, checkpoint, getters, zero
 cases u1; cases u2; cases u3; cases u5
 have rbP : RSL.readonlyBuffer (account n0) = .ok () :=
  (outerOk _ _ _ _ hrbP (NNH_AuthGuardPorts.buffer n0)).symm
 have rbU : RSL.readonlyBuffer (account n1) = .ok () :=
  (outerOk _ _ _ _ hrbU (NNH_AuthGuardPorts.buffer n1)).symm
 have ckm := NNH_ModelCheckpoint.value
  (NNH_MRegistryOps.install (NNH_LaneModel.install (S c)) LIB_Deployed.deployed (NNH_HostCtx.envOf c)) n2 program true
 have ckc := NNH_AuthGuardCongr.checkpoint (S c) (NGL_CheckpointModel.install
    (NNH_MRegistryOps.install (NNH_LaneModel.install (S c)) LIB_Deployed.deployed (NNH_HostCtx.envOf c)))
    (by rfl) (by rfl) (by rfl) n2 program true
 have ckV : NNH_ReturnedClone.checkpointValue (account n2) (key program) true = .ok () :=
  (outerOk _ _ _ _ (ckc.symm.trans hck) ckm).symm
 have gcb : NNH_ModelCarrier.outer _ (r1_pool_adapter.owned.OwnedAccount.data (S c) n2) = ok (account n2).bytes :=
  NNH_ModelCarrier.getter (S c) n2
 have ckRead : (account n2).bytes = .ok (bytes cb) := (outerOk _ _ _ _ hcb gcb).symm
 have gub : NNH_ModelCarrier.outer _ (r1_pool_adapter.owned.OwnedAccount.data (S c) n1) = ok (account n1).bytes :=
  NNH_ModelCarrier.getter (S c) n1
 have ubRead : (account n1).bytes = .ok (bytes ub) := (outerOk _ _ _ _ hub gub).symm
 have gpb : NNH_ModelCarrier.outer _ (r1_pool_adapter.owned.OwnedAccount.data (S c) n0) = ok (account n0).bytes :=
  NNH_ModelCarrier.getter (S c) n0
 have pbRead : (account n0).bytes = .ok (bytes pb) := (outerOk _ _ _ _ hpb gpb).symm
 have zV : RSL.requireZero (bytes cb) = .ok () :=
  (outerOk _ _ _ _ hz (NNH_Stage1ZeroCurrent.projection cb)).symm
 -- decode, validate, encode
 have hdec' : AspisS6CurrentCodecInstallation.decode ub = ok (.Ok st) := hdec
 obtain ⟨enc, _, encv⟩ := AspisS6CurrentCodecInstallation.accepted_inverse ub st hdec'
 have ubLen : (LIB_Carriers.bytes ub).length = 1880 := by
  rw [NOC_PrepareFront.bytes_length, ← encv]
  first | exact enc.property | (have := enc.property; scalar_tac) | simp
 have decL : C.decodeStatement (LIB_Carriers.bytes ub) = some (NNH_S1DecodeOk.carrier st) := by
  change LIBC_S1.decode (LIB_Carriers.bytes ub) = _
  unfold LIBC_S1.decode
  rw [dif_pos ubLen, LIBC_Bytes.from_native]
  unfold NMT_345.decodeCall
  rw [hdec']
  all_goals first | rfl | (simp only [NMT_345.mapOuter,NMT_345.mapCore]; done) | (simp [NMT_345.mapOuter,NMT_345.mapCore])
 cases u21
 have v21 : NNH_S1HostCodec.validate st = .ok (.Ok ()) := h21
 have vn := NOM_TerminalDomain.validate_native st v21
 have validL : C.validateStatement (NNH_S1DecodeOk.carrier st) = true := (LIBC_S1.valid_iff _).mpr vn
 have digest := NOM_TerminalDomain.validated_digest st v21
 have enc0 := NNX_CommonEncode.source c st
 rw [hcm, bind_tc_ok] at enc0
 have enc2 := enc0.symm.trans h24
 have encCall : NMT_345.encodeCall (NMT_345.commonValue (NNH_S1DecodeOk.carrier st)).lane_transition.candidate_afterstate =
   .ok (.Ok nat) := by
  revert enc2
  cases hE : NMT_345.encodeCall (NMT_345.commonValue (NNH_S1DecodeOk.carrier st)).lane_transition.candidate_afterstate with
  | ok r => cases r with
   | Ok o => intro e; first | (cases e; rfl) | (simp only at e; rw [e]) | simp_all
   | Err _ => intro e; first | (cases e; done) | simp at e
  | fail _ => intro e; first | (cases e; done) | simp at e
  | div => intro e; first | (cases e; done) | simp at e
 have encL : C.encodeCandidate (NNH_S1DecodeOk.carrier st) = some (nat.val.map NMT_345.byte) := by
  change LIBC_S1.encode _ = _
  unfold LIBC_S1.encode
  rw [encCall] <;> rfl
 -- proof guard
 have hlen' : Slice.len pb = 58295#usize := by
  first
   | (simpa [bne_iff_ne] using hlen)
   | (by_cases e : Slice.len pb = 58295#usize
      · exact e
      · exact absurd (by simp [e]) hlen)
 have pbLen : pb.val.length = 58295 := by have := congrArg UScalar.val hlen'; exact this
 obtain ⟨pre,preRun,preVal⟩ := NOC_Stage1Forward.prefixRead pb 688#usize
  (by change (688#usize).val ≤ pb.val.length; rw [pbLen]; scalar_tac)
 have es0 : s0 = pre := Result.ok.inj (hs0.symm.trans preRun)
 subst es0
 have hne' : core.slice.cmp.PartialEqSlice.ne core.cmp.PartialEqU8 s0 (Array.to_slice nat) = ok false := hne
 have snat := neConv _ _ hne'
 have takeEq : (bytes pb).take 688 = nat.val.map NMT_345.byte := by
  have nb : nat.val.map NMT_345.byte = nat.val.map byte :=
   List.map_congr_left (fun x _ => NOC_Stage1Forward.byteSame x)
  rw [nb]
  have sv : pb.val.slice 0 688 = nat.val := by
   have := congrArg Subtype.val snat
   rw [preVal] at this
   exact this
  rw [← sv]
  show List.take 688 (List.map byte pb.val) = List.map byte (List.slice 0 688 pb.val)
  first
   | (simp only [List.slice,List.map_take,List.drop_zero,Nat.sub_zero])
   | (simp [List.slice,List.map_take])
   | rfl
 have tagL : (bytes pb).getD 696 0 = 2 := by
  have inside : 696 < pb.val.length := by rw [pbLen]; decide
  obtain ⟨out,run,value⟩ := NNH_ResultWp.expose _ _ (Slice.index_usize_spec pb 696#usize inside)
  have et : t = out := Result.ok.inj (htag.symm.trans run)
  have t2 : t = 2#u8 := by
   first
    | (simpa [bne_iff_ne] using htv)
    | (by_cases e : t = 2#u8
       · exact e
       · exact absurd (by simp [e]) htv)
  show (pb.val.map byte).getD 696 0 = 2
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem inside]
  simp only [Option.map_some, Option.getD_some]
  rw [← value, ← et, t2]
  with_unfolding_all rfl
 have pbBytesLen : (bytes pb).length = 58295 := by
  rw [bytes_length]; exact pbLen
 have guard : ((bytes pb).length != 58295 || (bytes pb).take 688 != nat.val.map NMT_345.byte ||
   (bytes pb).getD 696 0 != (2 : UInt8)) = false := by
  rw [pbBytesLen, takeEq, tagL]; simp
 -- the child: first_decoded inverted to the installed tx1
 obtain ⟨sp', hsp', spEq⟩ := NOC_Stage1Forward.publicBinding st
 have esp : sp = sp' := Result.ok.inj (hsp.symm.trans hsp')
 subst esp
 have fd2 := hfd
 unfold first_decoded at fd2
 ncj_br fd2
 rw [NNH_Run5bCurrentInventory.adapter] at fd2
 unfold AspisS6CurrentFirstInstallation.current at fd2
 rw [spEq,AspisS6CurrentFirstInstallation.observer_none] at fd2
 have dg : AspisS6CurrentFirstInstallation.toDigest (SolanaDigest.Insts.Aspis_coreDigestDigest32 (S c)) =
  NNV_PreparedAtHost.digest c := rfl
 rw [dg] at fd2
 obtain ⟨x | _, htx, fdk⟩ := NOC_SemConv.bindInv fd2; rotate_left; nci_kill fdk
 obtain ⟨s1',s1Run,s1Same⟩ := NNH_SliceRangeOk.value pb 688#usize 58295#usize (by scalar_tac)
  (by change (58295#usize).val ≤ pb.val.length; rw [pbLen]; scalar_tac)
 have es1 : s1 = s1' := Result.ok.inj (hs1.symm.trans s1Run)
 subst es1
 have width : s1.val.length = 57607 := by
  have l := congrArg List.length s1Same
  rw [bytes_length] at l
  rw [l]
  simp only [RSL.slice,List.length_take,List.length_drop,bytes_length,pbLen]
  all_goals first | rfl | decide | omega | scalar_tac | simp
 have hproof : RSL.slice (bytes pb) RSL.AFTERSTATE_BYTES RSL.PROOF_ACCOUNT_BYTES = bytes s1 := by
  rw [s1Same] <;> rfl
 have hk10 : ((bytes data).getD 1 0).toNat = 10 := by rw [dataEq]; rfl
 obtain ⟨out, hout⟩ := NOC_Tx1Conv.tx1 c
  ⟨C.semanticPublic (NNH_S1DecodeOk.carrier st),bytes ub,
   RSL.slice (bytes pb) RSL.AFTERSTATE_BYTES RSL.PROOF_ACCOUNT_BYTES,((bytes data).getD 1 0).toNat⟩
  ub s1 hproof hk10 width digest ⟨x, htx⟩
 obtain ⟨v',tx1Run,vEq⟩ := NOC_Tx1Forward.source c _ ub s1 10#usize rfl hproof hk10 width _ hout
 have fwdFd := NOC_Stage1Forward.fdLemma c st (NNH_S1DecodeOk.carrier st) rfl sp spEq ub s1 v' tx1Run
 have evv : v = v' := core.result.Result.Ok.inj (Result.ok.inj (hfd.symm.trans fwdFd))
 subst evv
 have childL : NNH_Tx1ReturnedValues.mapVErrValue VL (NNH_Tx1Returns.values.tx1
   ⟨C.semanticPublic (NNH_S1DecodeOk.carrier st),bytes ub,
    RSL.slice (bytes pb) RSL.AFTERSTATE_BYTES RSL.PROOF_ACCOUNT_BYTES,((bytes data).getD 1 0).toNat⟩
   (NOC_Run5bCtx.envOf c)) = .ok (bytes v.deref) := by
  change NNH_Tx1ReturnedValues.mapVErrValue VL (NNH_Tx1Returns.value _ (NOC_Run5bCtx.envOf c)) = _
  rw [hout, ← vEq] <;> rfl
 have hsv' : alloc.vec.Vec.len v = Slice.len cb := by
  first
   | (simpa [bne_iff_ne] using hsv)
   | (by_cases e : alloc.vec.Vec.len v = Slice.len cb
      · exact e
      · exact absurd (by simp [e]) hsv)
 have savedLen : (bytes v.deref).length = (bytes cb).length := by
  have := congrArg UScalar.val hsv'
  simp only [bytes_length]
  exact this
 have pk : NNH_Stage1Cut.Packet ⟨key program,accounts xs,bytes data⟩ (account n0) (account n1) (account n2)
   (bytes v.deref) (NOC_Run5bCtx.envOf c) :=
  { distinct := distinctL
    proof_readonly := rbP
    public_readonly := rbU
    checkpoint_owned := ckV
    checkpoint_data := bytes cb
    checkpoint_read := ckRead
    checkpoint_zero := zV
    public_data := bytes ub
    public_read := ubRead
    statement := NNH_S1DecodeOk.carrier st
    decode := decL
    valid := validL
    candidate := nat.val.map NMT_345.byte
    encode := encL
    proof_data := bytes pb
    proof_read := pbRead
    proof_guard := guard
    child := childL
    saved_length := savedLen }
 show NNH_Stage1RefEval.value VL P NNH_Tx1Returns.values C _ _ = _
 simp only [NNH_Stage1RefEval.value,route,shape,if_false,Bool.false_eq_true,↓reduceIte]
 exact consume _ _ _ _ _ _ pk

#print axioms outerOk
#print axioms keyInj
#print axioms wadd
#print axioms distinct3
#print axioms neConv
#print axioms consume
#print axioms conv
end NOC_Stage1Conv
end
