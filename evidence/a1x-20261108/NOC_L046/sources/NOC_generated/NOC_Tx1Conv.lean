import NOC_PrepareConv
import NOC_Tx1Forward
import NOM_MerkleParent
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_Tx1Conv
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NOC_FinishSource

abbrev cur {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := NOC_Tx1Forward.cur c
abbrev M {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := NOC_Tx1Forward.M c

/-- Library batch value from an Ok NHT action of its model. -/
theorem batchValue (a : LIBC_BatchMerkle.Args) (env : RSL.Env)
 (h : NHT_ResultPort.action (LIBC_BatchMerkle.model a env) = ok (.Ok ())) :
 LIBC_BatchMerkle.value a env = .ok () := by
 unfold LIBC_BatchMerkle.value
 cases hm : LIBC_BatchMerkle.model a env with
 | ok r =>
  rw [hm] at h
  cases r with
  | Ok u => rfl
  | Err e => first | cases h | simp [NHT_ResultPort.action, NHT_ResultPort.reply] at h
 | fail e => rw [hm] at h; first | cases h | simp [NHT_ResultPort.action] at h
 | div => rw [hm] at h; first | cases h | simp [NHT_ResultPort.action] at h

/-- Converse of NOC_Tx1Forward.batch (op6) at k = 0 on the canonical queries,
through NOM_MerkleParent.hostParent; no LIBC_BatchMerkle.Domain premise. -/
theorem batch {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (proof : Slice U8)
 (p : LIB_VCarriers.Prepared) (folded : RSL.B32)
 (q : ∀ x ∈ p.queries.val, x.val < 262144)
 (h : (cur c).op6 (NNV_PreparedAtHost.digest c) proof (InstalledPreparation.currentPrepared p)
  (LIB_Env.nativeKey folded) 0#usize () = ok (.Ok ())) :
 LIBC_BatchMerkle.value (LIB_Carriers.bytes proof,p,folded,0) (NOC_Run5bCtx.envOf c) = .ok () := by
 have h' : Op5T_Install.mapResult Op5T_Install.currentError
   (Port3_NativeBatchBody.verifier.candidate.batch_merkle
    (Port3_BatchStd.install Port4B_Install.leaves)
    (VTop_Checkpoint.digest (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)))
    proof (NFW_PreparedPort.prepared p) (LIB_Env.nativeKey folded) 0#usize ()) = ok (.Ok ()) := h
 have inner : Port3_NativeBatchBody.verifier.candidate.batch_merkle
    (Port3_BatchStd.install Port4B_Install.leaves)
    (VTop_Checkpoint.digest (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)))
    proof (NFW_PreparedPort.prepared p) (LIB_Env.nativeKey folded) 0#usize () = ok (.Ok ()) := by
  cases hm : Port3_NativeBatchBody.verifier.candidate.batch_merkle
    (Port3_BatchStd.install Port4B_Install.leaves)
    (VTop_Checkpoint.digest (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)))
    proof (NFW_PreparedPort.prepared p) (LIB_Env.nativeKey folded) 0#usize () with
  | ok r =>
   rw [hm] at h'
   cases r with
   | Ok u => cases u; rfl
   | Err e => first | cases h' | simp [Op5T_Install.mapResult] at h'
  | fail e => rw [hm] at h'; first | cases h' | simp [Op5T_Install.mapResult] at h'
  | div => rw [hm] at h'; first | cases h' | simp [Op5T_Install.mapResult] at h'
 have acc : Port4B_Install.batch (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)) proof
   (NFW_PreparedPort.prepared p) (LIB_Env.nativeKey folded) 0#usize () = ok (.Ok ()) :=
  (Port3_QueryInstall.success_iff _ ()).mpr inner
 have q' : ∀ j, j<22 → (NFW_PreparedPort.prepared p).queries.val[j]!.val<262144 := by
  intro j hj
  have hl : j < p.queries.val.length := by have := p.queries.property; scalar_tac
  have m := List.getElem_mem hl
  show (p.queries.val[j]!).val < 262144
  have e : p.queries.val[j]! = p.queries.val[j] := by
   first
    | exact getElem!_pos p.queries.val j hl
    | (simp [List.getElem?_eq_getElem hl]; done)
    | (simp [hl]; rw [List.getElem?_eq_getElem hl]; rfl)
    | (simp; rw [List.getElem?_eq_getElem hl]; rfl)
  rw [e]
  exact q _ m
 have hp := NOM_MerkleParent.hostParent c proof (NFW_PreparedPort.prepared p) (LIB_Env.nativeKey folded)
  0#usize (by decide) q' acc
 apply batchValue
 rw [LIBC_BatchMerkle.source]
 have z : LIBC_Usize.raw 0 = 0#usize := LIBC_Usize.from_native 0#usize (by scalar_tac)
 rw [z,LIBC_Bytes.from_native]
 exact hp

/-- Converse of the op7 query step on the Domain: the native query and the
library value are images of the SAME query-loop Result. -/
theorem query {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (proof : Slice U8)
 (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) (acc : LIB_VCarriers.Acc)
 (geo : LIB_VCarriers.Geo) (pending : LIB_VCarriers.Weights)
 (d : LIBC_QueryLoop.Domain (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10))
 (out : Tx1Q_Carriers.C.A × Tx1Q_Carriers.C.B)
 (h : (cur c).op7 proof (InstalledPreparation.currentPrepared p)
  (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc acc)) (NNV_PreparedInputs.scratch g) none
  (Tx1Q_PrefixInstall.unGeometry geo) (Tx1Q_Carriers.unPending pending) 10#usize = ok (.Ok out)) :
 ∃ r, LIBC_QueryLoop.value (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10) (NOC_Run5bCtx.envOf c) = .ok r := by
 obtain ⟨hp1,hg1⟩ := Prod.mk.inj (NNV_CurrentQuerySource.prepared_input p g)
 have chain := (NNX_CurrentQuery.source (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation
   _ _ _ _ _ _ d.2.2.invariant d.2.1).trans
  ((NOC_QueryLink.loop _ _ _ _ _ _ d.2.2.gCanonical d.2.2.invariant d.2.1).trans
   (NFS_QueryLoopRoot.tx1 (NFS_CallerDomains.select LIBC_QueryOps.seed)
    (LIBC_Bytes.raw (LIB_Carriers.bytes proof))
    (LIBC_QueryLoop.nativeP (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10))
    (LIBC_QueryLoop.nativeA (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10))
    (LIBC_QueryLoop.nativeG (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10))
    (LIBC_QueryLoop.geo (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10))
    (LIBC_QueryLoop.pending (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10))
    0 0 d.2.2.gCanonical d.2.2.invariant d.2.1).symm)
 rw [LIBC_Bytes.from_native] at chain
 have src := NNV_CurrentQuerySource.source (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation proof
  (InstalledPreparation.currentPrepared p) (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc acc))
  (NNV_PreparedInputs.scratch g) (Tx1Q_PrefixInstall.unGeometry geo) (Tx1Q_Carriers.unPending pending) 10#usize
 rw [hp1,hg1,Tx1Q_Carriers.accumulator_roundtrip] at src
 have h2 := src.symm.trans h
 unfold Tx1Q_Install.result at h2
 obtain ⟨y | _, hy, h3⟩ := NOC_SemConv.bindInv h2; rotate_left; nci_kill h3
 have hy' := chain.symm.trans hy
 obtain ⟨y1, y2⟩ := y
 refine ⟨?v, ?_⟩
 rotate_left
 unfold LIBC_QueryLoop.value LIBC_QueryLoop.model
 change LIBC_ResultGraph.value LIBC_QueryLoop.port (.error .Query)
  (Port3_QueryInstall.result (NNX_QueryOutput.run (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10))) = _
 rw [hy']
 rfl

theorem splitOk {E : Type} {e : E} :
 (if ((10 : Nat) != RSL.SPLIT) = true then Except.error e else Except.ok ()) = Except.ok () := by
 first | rfl | decide | simp [RSL.SPLIT]

/-- Converse of NOC_Tx1Forward.source at k = 10 on the 57607-byte proof and a
validated public digest: an Ok installed current tx1 gives an ok returned
library 094 value. -/
theorem tx1 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (a : RSL.TX1_094.Args NNH_Tx1Returns.V)
 (pubBytes proof : Slice U8) (hproof : a.proof = LIB_Carriers.bytes proof) (hk : a.k = 10)
 (width : proof.val.length = 57607) (digest : LIB_VPublicDomain.publicDigestDom a.public_)
 (called : ∃ v, verifier.candidate.tx1 (cur c) (NNV_PreparedAtHost.digest c)
   (FirstComposition.toCurrentPublic a.public_) pubBytes proof 10#usize () none = .ok (.Ok v)) :
 ∃ out, NNH_Tx1Returns.value a (NOC_Run5bCtx.envOf c) = .ok out := by
 obtain ⟨v, h⟩ := called
 rcases a with ⟨pub, pb, pr, k⟩
 change pr = LIB_Carriers.bytes proof at hproof
 change k = 10 at hk
 subst hproof
 subst hk
 have ksplit : ((10#usize : Usize) != compact.SPLIT) = false := by
  first | (unfold compact.SPLIT; simp) | simp [compact.SPLIT] | rfl
 unfold verifier.candidate.tx1 at h
 rw [ksplit] at h
 ncj_nrh h
 -- op3, op4
 obtain ⟨variant | _, h3, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 have hparse := NOC_ConvLeaves.parse (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation
  proof variant h3 (NOC_Run5bCtx.envOf c)
 ncj_br h
 obtain ⟨u4 | _, h4, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 have hscan := NOC_Conv094.scan (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation
  proof width (by cases u4; exact h4) (NOC_Run5bCtx.envOf c)
 ncj_br h
 ncj_br h
 -- ZERO scratch and prepare
 obtain ⟨we, zr, zs⟩ := NOC_Tx1Forward.zero c
 ncj_step h zr
 obtain ⟨⟨p' | _, g1⟩, hprep, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 rw [zs] at hprep
 obtain ⟨pg, hpg⟩ := NOC_PrepareConv.prepare c pub proof width digest ⟨p', g1, hprep⟩
 have hpg' : NNH_Tx1Returns.preparedValue ⟨pub,LIB_Carriers.bytes proof,LIB_Instances.VL.zeroE29⟩
   (NOC_Run5bCtx.envOf c) = .ok (pg.1,pg.2) := hpg
 have fwd := NOC_PrepareFront.source c pub proof LIB_Instances.VL.zeroE29 pg.2 pg.1 width hpg'
 obtain ⟨e1, e2⟩ := Prod.mk.inj (Result.ok.inj (hprep.symm.trans fwd))
 have e1' := core.result.Result.Ok.inj e1
 subst e1'
 subst e2
 ncj_nrh h
 ncj_br h
 -- op20
 obtain ⟨acc' | _, h20, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 have hacc0 := NOC_Conv094.accNew (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation acc' h20
 generalize hA : LIBC_VStateCarriers.fromAcc (Tx1Q_Carriers.accumulator acc') = acc at hacc0
 have hacc : LIB_VLib.accNewValue () (NOC_Run5bCtx.envOf c) = .ok acc := hacc0
 obtain ⟨native,_,same,op20⟩ := NNH_Run5bCurrentInitial.returned (M c) (NNH_HostCtx.envOf c)
  c.fixed.indexError c.fixed.reservation acc hacc
 have op20' : (cur c).op20 .S2 = ok (.Ok (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc acc))) := by
  rw [same,LIBC_VStateCarriers.to_from_acc]; exact op20
 have eA := core.result.Result.Ok.inj (Result.ok.inj (h20.symm.trans op20'))
 subst eA
 ncj_nrh h
 ncj_br h
 ncj_br h
 -- folded root
 ncj_step h (NOC_Tx1Forward.off_folded c)
 ncj_step h (NOC_Tx1Forward.off_round1 c)
 obtain ⟨s,srun,ssame⟩ := NNH_SliceRangeOk.value proof 7751#usize 7783#usize (by scalar_tac)
  (by change (7783#usize).val ≤ proof.val.length; scalar_tac)
 ncj_step h srun
 obtain ⟨tr, htr, h⟩ := NOC_SemConv.bindInv h
 obtain ⟨fr, hu, h⟩ := NOC_SemConv.bindInv h
 cases tr with
 | Err e => nci_kill hu
 | Ok arr =>
 obtain ⟨folded0, hroot⟩ := NOC_SemConv.rootConv s arr htr
 have es : LIB_Carriers.bytes s = RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_FOLDED_ROOT RSL.OFF_ROUND1 := ssame
 have hf : RSL.TX1_136.toB32 (RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_FOLDED_ROOT RSL.OFF_ROUND1) = some folded0 := by
  rw [← es]; exact hroot
 have copy := NNX_RootCopy.source s folded0 hroot
 have eArr := core.result.Result.Ok.inj (Result.ok.inj (htr.symm.trans copy))
 subst eArr
 cases hu
 ncj_nrh h
 -- domains from the SAME returned prepare law
 obtain ⟨sem,vw,_,prepCalled⟩ := NNV_PreparedFront.returned _ _ pg.1 pg.2 hpg'
 have law := NOC_QueryDomain.prepared _ (NOC_Run5bCtx.envOf c) pg.1 pg.2
  (NOC_Tx1Forward.lawOf _ _ pg.1 pg.2 prepCalled)
 have gd := NNG_GeometryDomain094.reached _ (NOC_Run5bCtx.envOf c) pg.1 pg.2 _ law
 -- op6
 obtain ⟨u6 | _, h6, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 have hbatch := batch c proof pg.1 folded0 gd.2.2.2.1 (by cases u6; exact h6)
 ncj_br h
 ncj_br h
 -- op19
 have z : LIBC_Usize.raw 0 = 0#usize := LIBC_Usize.from_native 0#usize (by scalar_tac)
 have t : LIBC_Usize.raw 10 = 10#usize := LIBC_Usize.from_native 10#usize (by scalar_tac)
 obtain ⟨g' | _, h19, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 obtain ⟨geo, hgeo, hgeq⟩ := NOC_Conv094.geometry (M c) (NNH_HostCtx.envOf c) c.fixed.indexError
  c.fixed.reservation pg.1 0 10 g' (by rw [z,t]; exact h19)
 subst hgeq
 ncj_br h
 -- op18
 have initial : LIBC_AccNew.child.run () (NOC_Run5bCtx.envOf c) ⟨.ret (.ok acc),[]⟩ :=
  ⟨trivial,(NOC_QueryDomain.graphRet _ _ _ _ [] hacc0 (by intro h; cases h)).symm⟩
 have w64 := (NNG_AccumulatorDomain094.weights_domain (NOC_Run5bCtx.envOf c) acc [] initial).1
 obtain ⟨pd' | _, h18, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 have hpend0 := NOC_Conv094.weightsNew (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation
  acc w64 pd' h18
 generalize hP : Tx1Q_Carriers.pending pd' = pending at hpend0
 have op18 := NNH_Run5bCurrentPending.source (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation
  acc pending w64 hpend0
 have eP := core.result.Result.Ok.inj (Result.ok.inj (h18.symm.trans op18))
 subst eP
 ncj_br h
 -- op7
 have w : (LIB_Carriers.bytes proof).length = 57607 := (NOC_PrepareFront.bytes_length proof).trans width
 have d := NOC_QueryDomain.domain _ (LIB_Carriers.bytes proof) w (NOC_Run5bCtx.envOf c) pg.1 pg.2 acc geo pending
  (NOC_Tx1Forward.lawOf _ _ pg.1 pg.2 prepCalled) hacc0 hgeo hpend0
 obtain ⟨r' | _, h7, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 obtain ⟨r, hr⟩ := query c proof pg.1 pg.2 acc geo pending d r' h7
 -- library value (finish and checkpoint are total)
 refine ⟨?v, ?_⟩
 rotate_left
 unfold NNH_Tx1Returns.value
 refine (NOC_SemConv.bvStep splitOk).trans ?_
 refine (NOC_SemConv.bvStep hparse).trans ?_
 refine (NOC_SemConv.bvStep hscan).trans ?_
 refine (NOC_SemConv.bvStep hpg).trans ?_
 refine (NOC_SemConv.bvStep hacc).trans ?_
 simp only [hf]
 refine (NOC_SemConv.bvStep hbatch).trans ?_
 refine (NOC_SemConv.bvStep hgeo).trans ?_
 refine (NOC_SemConv.bvStep hpend0).trans ?_
 refine (NOC_SemConv.bvStep hr).trans ?_
 refine (NOC_SemConv.bvStep rfl).trans ?_
 refine (NOC_SemConv.bvStep rfl).trans ?_
 rfl

#print axioms batchValue
#print axioms batch
#print axioms query
#print axioms splitOk
#print axioms tx1
end AspisR1.NOC_Tx1Conv
end
