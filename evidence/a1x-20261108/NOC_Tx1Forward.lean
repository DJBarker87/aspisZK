import NOC_Tx1Cut
import NOC_PrepareFront
import NOC_QueryLink
import NOC_QueryDomain
import NOC_MerkleBounded
import NOC_Conv094
import NNX_Flush
import NNX_RootCopy
import NNV_CurrentCheckpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_Tx1Forward
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NOC_FinishSource

abbrev cur {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := NOC_PrepareFront.cur c
abbrev M {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation

/-- The ZERO scratch of the native body is the library's zeroE29 scratch. -/
theorem zero {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 ∃ we, AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO (cur c) = ok we ∧
  Array.repeat 29#usize we = NNV_PreparedInputs.scratch LIB_Instances.VL.zeroE29 := by
 refine ⟨{c0:={c0:={a:=0#u32,b:=0#u32},c1:={a:=0#u32,b:=0#u32}},
   c1:={c0:={a:=0#u32,b:=0#u32},c1:={a:=0#u32,b:=0#u32}}},?_,?_⟩
 · unfold AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact.ZERO
   have h0 : @AspisR1CurrentCaller.Ops.op0 (cur c) = ok {c0:={a:=0#u32,b:=0#u32},c1:={a:=0#u32,b:=0#u32}} := by
    first | rfl | with_unfolding_all rfl
   rw [h0]
   all_goals first | rfl | with_unfolding_all rfl
 · apply Subtype.ext
   show List.replicate 29 _ = List.map InstalledPreparation.currentE
    (List.replicate 29 AspisR1PublicPreparation.aspis_core.field.WideExact.ZERO)
   rw [List.map_replicate]
   congr 1
   all_goals first | rfl | with_unfolding_all rfl | (unfold InstalledPreparation.currentE InstalledPreparation.currentQ; with_unfolding_all rfl)

theorem off_folded {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 compact.OFF_FOLDED_ROOT (cur c) = ok 7751#usize := by
 unfold compact.OFF_FOLDED_ROOT
 change (do let i ← ok 7527#usize; i + 224#usize) = ok 7751#usize
 simp only [bind_tc_ok]
 apply UsizeArithmetic.add_eq_ok <;> scalar_tac
theorem off_round1 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 compact.OFF_ROUND1 (cur c) = ok 7783#usize := by
 unfold compact.OFF_ROUND1
 rw [off_folded]
 simp only [bind_tc_ok]
 apply UsizeArithmetic.add_eq_ok <;> scalar_tac

/-- Folded-root window and its 32-byte copy, from the SAME library toB32. -/
theorem foldedRoot (proof : Slice U8) (width : proof.val.length = 57607) (folded : RSL.B32)
 (h : RSL.TX1_136.toB32 (RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_FOLDED_ROOT RSL.OFF_ROUND1) = some folded) :
 ∃ s, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
   {start := 7751#usize, «end» := 7783#usize} = ok s ∧
  core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 s =
   ok (.Ok (LIB_Env.nativeKey folded)) := by
 obtain ⟨s,run,same⟩ := NNH_SliceRangeOk.value proof 7751#usize 7783#usize (by scalar_tac)
  (by change (7783#usize).val ≤ proof.val.length; scalar_tac)
 refine ⟨s,run,NNX_RootCopy.source s folded ?_⟩
 have e : LIB_Carriers.bytes s = RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_FOLDED_ROOT RSL.OFF_ROUND1 := same
 rw [e]; exact h

theorem resultOk (m : Result (core.result.Result Unit AspisR1Stage2.verifier.Error))
 (h : Port3_QueryInstall.result m = ok (.Ok ())) : m = ok (.Ok ()) := by
 cases m with
 | ok v =>
  cases v with
  | Ok x => cases x; rfl
  | Err e => first | cases h | simp [Port3_QueryInstall.result] at h
 | fail e => first | cases h | simp [Port3_QueryInstall.result] at h
 | div => first | cases h | simp [Port3_QueryInstall.result] at h

/-- op6 forward at k = 0 from the SAME returned library batch value. Only
k = 0 and the canonical queries are used (no LIBC_BatchMerkle.Domain premise). -/
theorem batch {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (proof : Slice U8)
 (p : LIB_VCarriers.Prepared) (folded : RSL.B32)
 (q : ∀ x ∈ p.queries.val, x.val < 262144)
 (called : LIB_VLib.batchMerkleValue (LIB_Carriers.bytes proof,p,folded,0) (NOC_Run5bCtx.envOf c) = .ok ()) :
 (cur c).op6 (NNV_PreparedAtHost.digest c) proof (InstalledPreparation.currentPrepared p)
  (LIB_Env.nativeKey folded) 0#usize () = ok (.Ok ()) := by
 have v : LIBC_BatchMerkle.value (LIB_Carriers.bytes proof,p,folded,0) (NOC_Run5bCtx.envOf c) = .ok () := called
 unfold LIBC_BatchMerkle.value at v
 obtain ⟨reply,model,image⟩ := NNH_Run5bReturnedGraph.ok _ _ _ () v
 cases reply with
 | Err e => cases image
 | Ok u =>
  cases u
  rw [LIBC_BatchMerkle.source] at model
  have z : LIBC_Usize.raw 0 = 0#usize := LIBC_Usize.from_native 0#usize (by scalar_tac)
  rw [z,LIBC_Bytes.from_native] at model
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
  have hp := NOC_MerkleBounded.hostParent c proof (NFW_PreparedPort.prepared p) (LIB_Env.nativeKey folded)
   0#usize (by decide) q' ((congrArg NHT_ResultPort.action model).trans rfl)
  have inner : Port3_NativeBatchBody.verifier.candidate.batch_merkle
    (Port3_BatchStd.install Port4B_Install.leaves)
    (VTop_Checkpoint.digest (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)))
    proof (NFW_PreparedPort.prepared p) (LIB_Env.nativeKey folded) 0#usize () = ok (.Ok ()) :=
   resultOk _ hp
  show Op5T_Install.mapResult Op5T_Install.currentError
    (Port3_NativeBatchBody.verifier.candidate.batch_merkle
    (Port3_BatchStd.install Port4B_Install.leaves)
    (VTop_Checkpoint.digest (Tx1Q_Install.digest (NNV_PreparedAtHost.digest c)))
    proof (NFW_PreparedPort.prepared p) (LIB_Env.nativeKey folded) 0#usize ()) = ok (.Ok ())
  rw [inner]
  all_goals rfl

/-- op7 forward on the derived query Domain, at the native carriers. -/
theorem query {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (proof : Slice U8)
 (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29) (acc : LIB_VCarriers.Acc)
 (geo : LIB_VCarriers.Geo) (pending : LIB_VCarriers.Weights) (r : LIB_VCarriers.Acc × LIB_VCarriers.Weights)
 (d : LIBC_QueryLoop.Domain (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10))
 (called : LIBC_QueryLoop.value (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10) (NOC_Run5bCtx.envOf c) = .ok r) :
 (cur c).op7 proof (InstalledPreparation.currentPrepared p)
  (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc acc)) (NNV_PreparedInputs.scratch g) none
  (Tx1Q_PrefixInstall.unGeometry geo) (Tx1Q_Carriers.unPending pending) 10#usize =
 ok (.Ok (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc r.1),Tx1Q_Carriers.unPending r.2)) := by
 have run := NOC_QueryLink.current (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation
  _ (NOC_Run5bCtx.envOf c) d r.1 r.2 called
 rw [LIBC_Bytes.from_native] at run
 obtain ⟨hp1,hg1⟩ := Prod.mk.inj (NNV_CurrentQuerySource.prepared_input p g)
 refine (NNV_CurrentQuerySource.source (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation proof
  (InstalledPreparation.currentPrepared p) (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc acc))
  (NNV_PreparedInputs.scratch g) (Tx1Q_PrefixInstall.unGeometry geo) (Tx1Q_Carriers.unPending pending) 10#usize).trans ?_
 rw [hp1,hg1,Tx1Q_Carriers.accumulator_roundtrip]
 exact congrArg (Tx1Q_Install.result (fun x : Tx1Q_Carriers.S.A × Tx1Q_Carriers.S.B =>
  (Tx1Q_Carriers.unAccumulator x.1,Tx1Q_Carriers.unPending x.2))) run

/-- The native flushed accumulator is the library finish value. -/
theorem finish_acc (after : LIB_VCarriers.Acc) (pend : LIB_VCarriers.Weights) (env : RSL.Env) :
 {Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc after) with
   weights := (alloc.vec.Vec.deref_mut (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc after)).weights).2
    (Tx1Q_Carriers.slice Tx1Q_Carriers.unK (NJJ_Flush.output pend))} =
 Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc (LIBC_Finish.value (pend,after) env)) := by
 have w : LIBC_VStateCarriers.mapVec LIBC_VStateCarriers.q
   (LIBC_VStateCarriers.mapVec LIBC_VStateCarriers.fromQ
    (⟨(NJJ_Flush.output pend).val,(NJJ_Flush.output pend).property⟩ :
      alloc.vec.Vec AspisR1Stage2.aspis_core.field.QM31)) =
   ⟨(NJJ_Flush.output pend).val,(NJJ_Flush.output pend).property⟩ := by
  apply Subtype.ext
  show ((NJJ_Flush.output pend).val.map LIBC_VStateCarriers.fromQ).map LIBC_VStateCarriers.q =
   (NJJ_Flush.output pend).val
  simp only [List.map_map,Function.comp_def,LIBC_VStateCarriers.to_from_q]
  exact List.map_id _
 show _ = Tx1Q_Carriers.unAccumulator ⟨LIBC_VStateCarriers.mapVec LIBC_VStateCarriers.q
   (LIBC_VStateCarriers.mapVec LIBC_VStateCarriers.fromQ
    ⟨(NJJ_Flush.output pend).val,(NJJ_Flush.output pend).property⟩),
   LIBC_VStateCarriers.e after.rhs,LIBC_VStateCarriers.q after.power,after.next⟩
 rw [w]
 all_goals rfl

/-- The SAME returned 087 law value in LIBC form. -/
theorem lawOf (x : RSL.Verified LIB_VLib.library × LIB_VCarriers.View × LIB_VCarriers.E29) (env : RSL.Env)
 (p : LIB_VCarriers.Prepared) (g : LIB_VCarriers.E29)
 (h : LIB_Prepared.value x env = (.ok p,g)) :
 LIBC_PreparedLaw.value (LIBC_PreparedCarriers.input LIB_Prepared.types x) env = (.ok p,g) := by
 have normalized : ∀ out, LIB_Prepared.output out = out := by
  intro out; rcases out with ⟨out,g⟩; cases out <;> rfl
 exact (normalized _).symm.trans h

/-- 094 forward at the corrected host: a returned library 094 value is the
installed current tx1's Ok result, with the SAME output bytes. No domain,
width, success or representation premise beyond the carrier identifications
of the arguments and the 57607-byte proof width, which the 345 caller
discharges from its own proof guard (NNH_Stage1ProofDomain.extent). -/
theorem source {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (a : RSL.TX1_094.Args NNH_Tx1Returns.V)
 (pubBytes proof : Slice U8) (k : Usize)
 (hpub : a.public_bytes = LIB_Carriers.bytes pubBytes) (hproof : a.proof = LIB_Carriers.bytes proof)
 (hk : a.k = k.val) (width : proof.val.length = 57607) (out : RSL.Bytes)
 (called : NNH_Tx1Returns.value a (NOC_Run5bCtx.envOf c) = .ok out) :
 ∃ v : alloc.vec.Vec U8,
  verifier.candidate.tx1 (cur c) (NNV_PreparedAtHost.digest c)
   (FirstComposition.toCurrentPublic a.public_) pubBytes proof k () none = .ok (.Ok v) ∧
  LIB_Carriers.bytes (alloc.vec.Vec.deref v) = out := by
 obtain ⟨pk⟩ := NOC_Tx1Cut.returned a _ out called
 obtain ⟨split,hparse,hscan,p,g,hprep,acc,hacc,folded,hf,hbatch,geo,hgeo,pending,hpend,r,hr,out_eq⟩ := pk
 have ak10 : a.k = 10 := bne_eq_false_iff_eq.mp split
 have kv : k.val = 10 := hk.symm.trans ak10
 have ks : k = 10#usize := UScalar.eq_of_val_eq (by first | (rw [kv]; scalar_tac) | rw [kv] | scalar_tac)
 subst ks
 rw [hproof] at hparse
 rw [hproof] at hscan
 rw [hproof] at hprep
 rw [hproof] at hf
 rw [hproof] at hbatch
 rw [hproof,ak10] at hr
 rw [ak10] at hgeo
 rw [hproof,hpub] at out_eq
 refine ⟨⟨(LIBC_Checkpoint.output (p,LIBC_Finish.value (r.2,r.1) (NOC_Run5bCtx.envOf c),
     LIB_Carriers.bytes proof,LIB_Carriers.bytes pubBytes) (NOC_Run5bCtx.envOf c)).val,
   (LIBC_Checkpoint.output (p,LIBC_Finish.value (r.2,r.1) (NOC_Run5bCtx.envOf c),
     LIB_Carriers.bytes proof,LIB_Carriers.bytes pubBytes) (NOC_Run5bCtx.envOf c)).property⟩,?_,out_eq.symm⟩
 -- children
 obtain ⟨variant,op3⟩ := NNH_Run5bCurrentShape.parse (M c) (NNH_HostCtx.envOf c) c.fixed.indexError
  c.fixed.reservation proof hparse
 have op4 := NNV_CurrentScan.returned (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation
  proof width hscan
 obtain ⟨we,zr,zs⟩ := zero c
 have prep : verifier.candidate.prepare (cur c) (NNV_PreparedAtHost.digest c)
   (FirstComposition.toCurrentPublic a.public_) proof () none (Array.repeat 29#usize we) =
   .ok (.Ok (InstalledPreparation.currentPrepared p),NNV_PreparedInputs.scratch g) := by
  rw [zs]; exact NOC_PrepareFront.source c a.public_ proof _ g p width hprep
 obtain ⟨native,_,same,op20⟩ := NNH_Run5bCurrentInitial.returned (M c) (NNH_HostCtx.envOf c)
  c.fixed.indexError c.fixed.reservation acc hacc
 have op20' : (cur c).op20 .S2 = ok (.Ok (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc acc))) := by
  rw [same,LIBC_VStateCarriers.to_from_acc]; exact op20
 obtain ⟨s,srun,stry⟩ := foldedRoot proof width folded hf
 -- domains from the SAME returned prepare and children
 obtain ⟨sem,vw,_,prepCalled⟩ := NNV_PreparedFront.returned _ _ p g hprep
 have law := NOC_QueryDomain.prepared _ (NOC_Run5bCtx.envOf c) p g (lawOf _ _ p g prepCalled)
 have gd := NNG_GeometryDomain094.reached _ (NOC_Run5bCtx.envOf c) p g _ law
 have op6 := batch c proof p folded gd.2.2.2.1 hbatch
 have g19 := NNV_CurrentGeometry.returned (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation
  p 0 10 geo hgeo
 have z : LIBC_Usize.raw 0 = 0#usize := LIBC_Usize.from_native 0#usize (by scalar_tac)
 have t : LIBC_Usize.raw 10 = 10#usize := LIBC_Usize.from_native 10#usize (by scalar_tac)
 rw [z,t] at g19
 have ha : LIBC_AccNew.value (NOC_Run5bCtx.envOf c) = .ok acc := hacc
 have hg : LIBC_Geometry.value (p,0,10) (NOC_Run5bCtx.envOf c) = .ok geo := hgeo
 have hb : LIBC_WeightsNew.value acc (NOC_Run5bCtx.envOf c) = .ok pending := hpend
 have initial : LIBC_AccNew.child.run () (NOC_Run5bCtx.envOf c) ⟨.ret (.ok acc),[]⟩ :=
  ⟨trivial,(NOC_QueryDomain.graphRet _ _ _ _ [] ha (by intro h; cases h)).symm⟩
 have w64 := (NNG_AccumulatorDomain094.weights_domain (NOC_Run5bCtx.envOf c) acc [] initial).1
 have op18 := NNH_Run5bCurrentPending.source (M c) (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation
  acc pending w64 hpend
 have w : (LIB_Carriers.bytes proof).length = 57607 := (NOC_PrepareFront.bytes_length proof).trans width
 have d := NOC_QueryDomain.domain _ (LIB_Carriers.bytes proof) w (NOC_Run5bCtx.envOf c) p g acc geo pending
  (lawOf _ _ p g prepCalled) ha hg hb
 have hr' : LIBC_QueryLoop.value (LIB_Carriers.bytes proof,p,acc,g,geo,pending,10) (NOC_Run5bCtx.envOf c) = .ok r := hr
 have op7 := query c proof p g acc geo pending r d hr'
 have op17 := NNX_Flush.source c _ d r.1 r.2 hr'
 have ck := NNV_CurrentCheckpoint.source c (p,LIBC_Finish.value (r.2,r.1) (NOC_Run5bCtx.envOf c),
  LIB_Carriers.bytes proof,LIB_Carriers.bytes pubBytes)
 rw [LIBC_Bytes.from_native,LIBC_Bytes.from_native] at ck
 have ck' : (cur c).op16 (NNV_PreparedAtHost.digest c) (InstalledPreparation.currentPrepared p)
   {Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc r.1) with
    weights := (alloc.vec.Vec.deref_mut (Tx1Q_Carriers.unAccumulator (LIBC_VStateCarriers.toAcc r.1)).weights).2
     (Tx1Q_Carriers.slice Tx1Q_Carriers.unK (NJJ_Flush.output r.2))} proof pubBytes () =
   .ok ⟨(LIBC_Checkpoint.output (p,LIBC_Finish.value (r.2,r.1) (NOC_Run5bCtx.envOf c),
     LIB_Carriers.bytes proof,LIB_Carriers.bytes pubBytes) (NOC_Run5bCtx.envOf c)).val,
    (LIBC_Checkpoint.output (p,LIBC_Finish.value (r.2,r.1) (NOC_Run5bCtx.envOf c),
     LIB_Carriers.bytes proof,LIB_Carriers.bytes pubBytes) (NOC_Run5bCtx.envOf c)).property⟩ := by
  rw [finish_acc _ _ (NOC_Run5bCtx.envOf c)]; exact ck
 have ksplit : ((10#usize : Usize) != compact.SPLIT) = false := by
  first | (unfold compact.SPLIT; simp) | simp [compact.SPLIT] | rfl
 -- the body
 unfold verifier.candidate.tx1
 rw [ksplit]
 noc_nrm
 noc_stp op3
 noc_nrm
 noc_stp op4
 noc_nrm
 noc_stp rfl
 noc_stp zr
 noc_nrm
 noc_stp prep
 noc_nrm
 noc_stp op20'
 noc_nrm
 noc_stp rfl
 noc_stp (off_folded c)
 noc_stp (off_round1 c)
 noc_stp srun
 noc_stp stry
 noc_stp rfl
 noc_stp op6
 noc_nrm
 noc_stp rfl
 noc_stp g19
 noc_nrm
 noc_stp op18
 noc_nrm
 noc_stp op7
 noc_nrm
 noc_stp rfl
 noc_nrm
 noc_stp op17
 noc_stp ck'
 noc_stp rfl
 rfl
#print axioms zero
#print axioms off_folded
#print axioms off_round1
#print axioms foldedRoot
#print axioms resultOk
#print axioms batch
#print axioms query
#print axioms finish_acc
#print axioms lawOf
#print axioms source
end AspisR1.NOC_Tx1Forward
end
