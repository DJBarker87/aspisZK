import NOC_Tx1Conv
import NOC_Stage1Forward
set_option autoImplicit false
noncomputable section
namespace NOC_Stage1Inv
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
 have k0 : NGL_DistinctInduction.keyAt (Array.make 3#usize [pa,pb,pc]) 0#usize = some pa.key := rfl
 have k1 : NGL_DistinctInduction.keyAt (Array.make 3#usize [pa,pb,pc]) 1#usize = some pb.key := rfl
 have k2 : NGL_DistinctInduction.keyAt (Array.make 3#usize [pa,pb,pc]) 2#usize = some pc.key := rfl
 have v0 : (0#usize : Usize).val = 0 := rfl
 have v1 : (1#usize : Usize).val = 1 := rfl
 have v2 : (2#usize : Usize).val = 2 := rfl
 have v3 : (3#usize : Usize).val = 3 := rfl
 refine ⟨?_,?_,?_⟩ <;> intro e <;> by_cases c01 : pa.key = pb.key <;> by_cases c02 : pa.key = pc.key <;>
  simp only [NGL_DistinctInduction.reference,NGL_DistinctInduction.outer,NGL_DistinctInduction.inner,
   k0,k1,k2,v0,v1,v2,v3,a0,a1,a2,e,c01,c02,Option.some.injEq,eq_self_iff_true,if_true,if_false,
   ↓reduceIte,bind_tc_ok,not_false_eq_true] at h <;>
  first | (cases h; done) | (simp at h; done) | simp_all

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


/-- Every native call of the frozen 345 body, read off an Ok reply. -/
structure Facts {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8) where
 hcmp : (S c).op1 core.cmp.PartialEqU8 data (Array.make 2#usize [3#u8,10#u8]) = ok true
 hl : (Slice.len xs != 3#usize) = false
 pa : r1_pool_adapter.owned.OwnedAccount
 pba : r1_pool_adapter.owned.OwnedAccount
 cka : r1_pool_adapter.owned.OwnedAccount
 i0 : Slice.index_usize xs 0#usize = ok pa
 i1 : Slice.index_usize xs 1#usize = ok pba
 i2 : Slice.index_usize xs 2#usize = ok cka
 hdist : r1_pool_adapter.owned.require_distinct_accounts (S c) (Array.make 3#usize [pa,pba,cka]) = ok (.Ok ())
 hrbP : r1_pool_adapter.owned.require_readonly_buffer pa = ok (.Ok ())
 hrbU : r1_pool_adapter.owned.require_readonly_buffer pba = ok (.Ok ())
 hck : r1_pool_adapter.owned.require_verifier_checkpoint (S c) cka program true = ok (.Ok ())
 cb : Slice U8
 hcb : r1_pool_adapter.owned.OwnedAccount.data (S c) cka = ok (.Ok cb)
 hz : r1_pool_adapter.owned.require_zero cb = ok (.Ok ())
 ub : Slice U8
 hub : r1_pool_adapter.owned.OwnedAccount.data (S c) pba = ok (.Ok ub)
 st : NNH_S1HostCodec.Statement
 hdec : (S c).op47 ub = ok (.Ok st)
 h21 : (S c).op21 st = ok (.Ok ())
 nat : Array U8 688#usize
 enc : ∃ cm, aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.common st = ok cm ∧
   (S c).op24 cm.lane_transition.candidate_afterstate = ok (.Ok nat)
 pb : Slice U8
 hpb : r1_pool_adapter.owned.OwnedAccount.data (S c) pa = ok (.Ok pb)
 hlen : (Slice.len pb != 58295#usize) = false
 s0 : Slice U8
 hs0 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) pb {«end» := 688#usize} = ok s0
 hne : (S c).op0 core.cmp.PartialEqU8 s0 nat = ok false
 t : U8
 htag : Slice.index_usize pb 696#usize = ok t
 htv : (t != 2#u8) = false
 sp : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public
 hsp : aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1.semantic_public st = ok sp
 s1 : Slice U8
 hs1 : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) pb ⟨688#usize,58295#usize⟩ = ok s1
 d1v : U8
 hd1 : Slice.index_usize data 1#usize = ok d1v
 kk : Usize
 hkk : lift (UScalar.cast .Usize d1v) = ok kk
 hfd : first_decoded (S c) sp ub s1 kk = ok (.Ok saved)
 hsv : (alloc.vec.Vec.len saved != Slice.len cb) = false

theorem pbytes : _root_.AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES = ok 57607#usize := by
 unfold _root_.AdapterRw.aspis_r1_cost_probe.verifier.PROOF_BYTES; exact NOC_Stage1Forward.proofBytes
theorem hckd : lift (Usize.checked_add 688#usize 57607#usize) = ok (some 58295#usize) := by
 rw [NNH_Stage2Sizes.checkedEnd]; rfl
theorem off : lift (Usize.wrapping_add 688#usize 8#usize) = ok 696#usize := by
 have e : Usize.wrapping_add 688#usize 8#usize = 696#usize :=
  wadd _ _ _ (by scalar_tac) (by rw [UScalar.size_def]; scalar_tac)
 rw [e]; rfl

/-- Inversion of the frozen 345 body (native side only, no library facts). -/
theorem invert {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (program : solana_pubkey.Pubkey)
 (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8) (saved : alloc.vec.Vec U8)
 (called : r1_pool_adapter.owned.stage1_owned (S c) program xs data = .ok (.Ok saved)) :
 Nonempty (Facts c program xs data saved) := by
 have h := called
 unfold r1_pool_adapter.owned.stage1_owned at h
 obtain ⟨b, hcmp, h⟩ := NOC_SemConv.bindInv h
 ncj_nrh h
 split at h
 rotate_left; nci_kill h
 rename_i hb
 subst hb
 ncj_nrh h
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
 ncj_step h pbytes
 ncj_step h (NNH_Stage2Sizes.afterstate (S c))
 ncj_step h hckd
 ncj_br h
 ncj_br h
 split at h
 · nci_kill h
 rename_i hlen
 obtain ⟨s0, hs0, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨b1, hne, h⟩ := NOC_SemConv.bindInv h
 cases b1
 rotate_left; nci_kill h
 ncj_nrh h
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
 cases u0; cases u1; cases u2; cases u3; cases u5; cases u21
 exact ⟨⟨hcmp,Bool.eq_false_iff.mpr hl,pa,pba,cka,i0,i1,i2,hdist,hrbP,hrbU,hck,cb,hcb,hz,ub,hub,st,hdec,h21,
  nat,⟨cm,hcm,h24⟩,pb,hpb,Bool.eq_false_iff.mpr hlen,s0,hs0,hne,t,htag,Bool.eq_false_iff.mpr htv,
  sp,hsp,s1,hs1,d1v,hd1,kk,hkk,hfd,Bool.eq_false_iff.mpr hsv⟩⟩

#print axioms outerOk
#print axioms keyInj
#print axioms wadd
#print axioms distinct3
#print axioms neConv
#print axioms consume
#print axioms pbytes
#print axioms hckd
#print axioms off
#print axioms invert
end NOC_Stage1Inv
end
