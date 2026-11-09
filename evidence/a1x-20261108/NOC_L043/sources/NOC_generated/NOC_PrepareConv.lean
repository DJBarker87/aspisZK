import NOC_SemConv
import NOC_PrepareFront
import NOC_ConvLeaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_PrepareConv
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NOC_FinishSource

/-- Hypothesis normalization without any `?`/mark rewriting: beta, tuple
matches, `ok` binds and decided Boolean guards only. -/
syntax "ncj_nrh " ident : tactic
macro_rules
 | `(tactic| ncj_nrh $h) => `(tactic| ((try simp only [Aeneas.Std.uncurry_apply_pair] at $h:ident); (try simp only [Aeneas.Std.uncurry] at $h:ident); (try simp only [bind_tc_ok, Bool.false_eq_true, ↓reduceIte] at $h:ident); (try simp only [] at $h:ident)))

/-- Steps over exactly one head that evaluates to `ok _` (a `?` on a known
constructor, a mark on `none`, a map_err on Ok, a lift). -/
syntax "ncj_br " ident : tactic
macro_rules
 | `(tactic| ncj_br $h) => `(tactic| (replace $h:ident := AspisR1.NOC_SemConv.stepInv rfl $h; ncj_nrh $h))

/-- Steps one head by a full Result equality. -/
syntax "ncj_step " ident term : tactic
macro_rules
 | `(tactic| ncj_step $h $e) => `(tactic| first
   | (replace $h:ident := AspisR1.NOC_SemConv.stepInv $e $h; ncj_nrh $h)
   | (ncj_nrh $h; replace $h:ident := AspisR1.NOC_SemConv.stepInv $e $h; ncj_nrh $h))

abbrev cur {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) := NOC_PrepareFront.cur c
abbrev V := NNH_PrepareReturns.V

/-- Library consume: the SAME front packet is the front value. -/
theorem front (a : RSL.TX1_087.Args V) (env : RSL.Env) (sem : RSL.Verified V) (v : V.View)
 (p : NNV_PrepareFrontCut.Packet a env sem v) :
 NNH_PrepareReturns.frontValue a env = .ok (sem,v) := by
 unfold NNH_PrepareReturns.frontValue
 refine (NOC_SemConv.bvStep (NOC_SemConv.mapEOk _ p.filled)).trans ?_
 refine (NOC_SemConv.bvStep (NOC_SemConv.mapEOk _ p.expandedSemantic)).trans ?_
 refine (NOC_SemConv.bvStep (NOC_SemConv.mapEOk _ p.expandedValues)).trans ?_
 refine (NOC_SemConv.bvStep p.viewed).trans ?_
 refine (NOC_SemConv.bvStep (NOC_SemConv.mapEOk _ p.observed)).trans ?_
 rfl

/-- Library consume: front packet plus the SAME LIB_Prepared value. -/
theorem preparedOk (a : RSL.TX1_087.Args V) (env : RSL.Env) (sem : RSL.Verified V) (v : V.View)
 (p : NNV_PrepareFrontCut.Packet a env sem v) (pr : V.Prepared) (after : V.E29)
 (hl : LIB_Prepared.value (sem,v,a.g) env = (.ok pr,after)) :
 NNH_Tx1Returns.preparedValue a env = .ok (pr,after) := by
 unfold NNH_Tx1Returns.preparedValue NNH_PrepareReturns.value
 rw [front a env sem v p]
 first
  | (simp only [hl]; done)
  | (simp only []; rw [hl])
  | (simp only [hl]; rfl)
  | (simp [hl])

/-- Converse of NOC_PrepareFront.source (X4) at the zero scratch: an Ok
installed prepare front at the corrected host, on the 57607-byte proof and a
validated public digest, gives an ok returned library 087 value. -/
theorem prepare {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx)
 (pub : NNH_Libraries.VL.Public) (proof : Slice U8) (width : proof.val.length = 57607)
 (digest : LIB_VPublicDomain.publicDigestDom pub)
 (called : ∃ p' g1, verifier.candidate.prepare (cur c) (NNV_PreparedAtHost.digest c)
   (FirstComposition.toCurrentPublic pub) proof () none (NNV_PreparedInputs.scratch LIB_Instances.VL.zeroE29) =
   .ok (.Ok p',g1)) :
 ∃ pg, NNH_Tx1Returns.preparedValue ⟨pub,LIB_Carriers.bytes proof,LIB_Instances.VL.zeroE29⟩
  (NOC_Run5bCtx.envOf c) = .ok pg := by
 obtain ⟨p', g1, h⟩ := called
 -- native windows (as in NOC_PrepareFront.source)
 obtain ⟨s1,s1Run,s1Raw,s1Len⟩ := NOC_PrepareFront.window proof width 16#usize 7031#usize 16 7031
  (by scalar_tac) (by scalar_tac) (by decide) (by decide)
 obtain ⟨s2,s2Run,s2Raw,s2Len⟩ := NOC_PrepareFront.window proof width 7031#usize 7495#usize 7031 7495
  (by scalar_tac) (by scalar_tac) (by decide) (by decide)
 obtain ⟨left,right,back,splitRun,leftVal,rightVal,backVal⟩ :=
  NNG_Split087.split (alloc.vec.Vec.deref_mut (NOC_PrepareFront.zeros 14759#usize)).1 13831#usize
   (by simp only [NOC_PrepareFront.zeros,alloc.vec.Vec.deref_mut,List.length_replicate]; scalar_tac)
 have leftLen : left.val.length = 13831 := by
  rw [leftVal]; simp only [NOC_PrepareFront.zeros,alloc.vec.Vec.deref_mut,List.length_take,List.length_replicate]; scalar_tac
 have rightLen : right.val.length = 928 := by
  rw [rightVal]; simp only [NOC_PrepareFront.zeros,alloc.vec.Vec.deref_mut,List.length_drop,List.length_replicate]; scalar_tac
 have s1L : s1.val.length = 7015 := s1Len
 have s2L : s2.val.length = 464 := s2Len
 have expS := NNH_Run5bCurrentExpand.semantic (NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation)
  (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation s1 left s1L leftLen
 have expV : (cur c).op11 s2 right = ok (.Ok (),LIBC_ExpandValuesModel.output s2 right) :=
  NOC_PrepareFront.values s2 right (by rw [s2L]) (by rw [s2L,rightLen]) (by rw [s2L]; decide)
 have semOutLen : (LIBC_ExpandSemanticModel.output s1).val.length = 13831 := by
  simp only [LIBC_ExpandSemanticModel.output,List.length_ofFn]
 have valOutLen : (LIBC_ExpandValuesModel.output s2 right).val.length = 928 := by
  simp only [LIBC_ExpandValuesModel.output,List.length_ofFn,rightLen]
 have vecVal : ((alloc.vec.Vec.deref_mut (NOC_PrepareFront.zeros 14759#usize)).2
   (back (LIBC_ExpandSemanticModel.output s1,LIBC_ExpandValuesModel.output s2 right))).val =
   (LIBC_ExpandSemanticModel.output s1).val ++ (LIBC_ExpandValuesModel.output s2 right).val :=
  backVal _ _ (by rw [semOutLen,leftLen]) (by rw [valOutLen,rightLen])
 have windows := NOC_PrepareFront.recombined _ _ semOutLen _ vecVal
 -- inversion of the native body
 unfold verifier.candidate.prepare at h
 ncj_step h (NOC_PrepareFront.logical_semantic c)
 ncj_step h AspisR1.NOC_PrepareDiv.logical_y1
 ncj_step h AspisR1.NOC_PrepareDiv.logical_sum
 obtain ⟨vz | _, hz, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 obtain ⟨granted, vzv⟩ := NOC_ConvLeaves.filled c 14759#usize vz hz
 have vzEq : vz = NOC_PrepareFront.zeros 14759#usize := Subtype.ext vzv
 subst vzEq
 ncj_nrh h
 ncj_br h
 ncj_br h
 ncj_br h
 ncj_step h splitRun
 ncj_step h (NOC_PrepareFront.off_semantic c)
 ncj_step h (NOC_PrepareFront.off_y1 c)
 ncj_step h s1Run
 ncj_step h expS
 ncj_br h
 ncj_step h (NOC_PrepareFront.off_inactive c)
 ncj_step h s2Run
 ncj_step h expV
 ncj_br h
 ncj_step h windows.1
 ncj_step h windows.2
 obtain ⟨v' | _, hview, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 obtain ⟨vlib, hvw, hvv⟩ := NOC_ConvLeaves.view (NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation)
  (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation proof _ _ width semOutLen valOutLen v' hview
  (NOC_Run5bCtx.envOf c)
 subst hvv
 ncj_nrh h
 ncj_br h
 obtain ⟨s0 | _, hsem, h⟩ := NOC_SemConv.bindInv h; rotate_left; nci_kill h
 obtain ⟨sem, hobs⟩ := NOC_SemConv.op9 c pub (NNV_PreparedInputs.view vlib).semantic granted digest ⟨s0, hsem⟩
 have fwd := NOC_SeedTransfer.op9 c pub (NNV_PreparedInputs.view vlib).semantic sem hobs
 have e0 : s0 = NNV_PreparedInputs.sem sem :=
  core.result.Result.Ok.inj (Result.ok.inj (hsem.symm.trans fwd))
 subst e0
 ncj_nrh h
 ncj_br h
 ncj_br h
 ncj_br h
 obtain ⟨pr, after, hl, _, _⟩ := NOC_ConvLeaves.prepared c sem vlib LIB_Instances.VL.zeroE29 p' g1 h
 -- library packet at the SAME values
 have semB : LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output s1) =
   LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output
    (LIBC_Bytes.raw (RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_SEMANTIC RSL.OFF_Y1))) := by
  rw [s1Raw]
 have logicalDrop : (List.replicate (RSL.LOGICAL_SEMANTIC+RSL.LOGICAL_Y1) (0 : UInt8)).drop RSL.LOGICAL_SEMANTIC =
   List.replicate 928 (0 : UInt8) := by
  show List.drop 13831 (List.replicate (13831+928) (0 : UInt8)) = List.replicate 928 0
  rw [List.drop_replicate,Nat.add_sub_cancel_left]
 have rightRaw : right.val.length =
   (LIBC_Bytes.raw ((List.replicate (RSL.LOGICAL_SEMANTIC+RSL.LOGICAL_Y1) (0 : UInt8)).drop RSL.LOGICAL_SEMANTIC)).val.length := by
  rw [rightLen,logicalDrop,LIBC_Bytes.raw_length _ (by simp only [List.length_replicate]; scalar_tac)]
  all_goals simp only [List.length_replicate]
 have valB : LIB_Carriers.bytes (LIBC_ExpandValuesModel.output s2 right) =
   LIB_Carriers.bytes (LIBC_ExpandValuesModel.output
    (LIBC_Bytes.raw (RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_Y1 RSL.OFF_INACTIVE))
    (LIBC_Bytes.raw ((List.replicate (RSL.LOGICAL_SEMANTIC+RSL.LOGICAL_Y1) (0 : UInt8)).drop RSL.LOGICAL_SEMANTIC))) := by
  rw [s2Raw]
  exact congrArg LIB_Carriers.bytes (NOC_PrepareFront.values_congr _ right _ rightRaw)
 have l1 : (RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_Y1 RSL.OFF_INACTIVE).length = 464 := by
  first
   | (show (RSL.slice (LIB_Carriers.bytes proof) 7031 7495).length = 464
      simp only [RSL.slice,List.length_take,List.length_drop,NOC_PrepareFront.bytes_length,width]
      done)
   | (show (RSL.slice (LIB_Carriers.bytes proof) 7031 7495).length = 464
      simp only [RSL.slice,List.length_take,List.length_drop,NOC_PrepareFront.bytes_length,width]
      omega)
   | (show (RSL.slice (LIB_Carriers.bytes proof) 7031 7495).length = 464
      simp [RSL.slice,NOC_PrepareFront.bytes_length,width])
 have l2 : ((List.replicate (RSL.LOGICAL_SEMANTIC+RSL.LOGICAL_Y1) (0 : UInt8)).drop RSL.LOGICAL_SEMANTIC).length = 928 := by
  rw [logicalDrop, List.length_replicate]
 have viewedLib : LIB_VLib.wideViewValue (LIB_Carriers.bytes proof,
   LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output
    (LIBC_Bytes.raw (RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_SEMANTIC RSL.OFF_Y1))),
   LIB_Carriers.bytes (LIBC_ExpandValuesModel.output
    (LIBC_Bytes.raw (RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_Y1 RSL.OFF_INACTIVE))
    (LIBC_Bytes.raw ((List.replicate (RSL.LOGICAL_SEMANTIC+RSL.LOGICAL_Y1) (0 : UInt8)).drop RSL.LOGICAL_SEMANTIC))))
   (NOC_Run5bCtx.envOf c) = .ok vlib := by
  rw [← semB, ← valB]; exact hvw
 have pk : NNV_PrepareFrontCut.Packet ⟨pub,LIB_Carriers.bytes proof,LIB_Instances.VL.zeroE29⟩
   (NOC_Run5bCtx.envOf c) sem vlib :=
  { logical := List.replicate (RSL.LOGICAL_SEMANTIC+RSL.LOGICAL_Y1) (0 : UInt8)
    semantic := LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output
     (LIBC_Bytes.raw (RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_SEMANTIC RSL.OFF_Y1)))
    y1 := LIB_Carriers.bytes (LIBC_ExpandValuesModel.output
     (LIBC_Bytes.raw (RSL.slice (LIB_Carriers.bytes proof) RSL.OFF_Y1 RSL.OFF_INACTIVE))
     (LIBC_Bytes.raw ((List.replicate (RSL.LOGICAL_SEMANTIC+RSL.LOGICAL_Y1) (0 : UInt8)).drop RSL.LOGICAL_SEMANTIC)))
    filled := NOC_ConvLeaves.filled_value (NOC_Run5bCtx.envOf c) _ granted
    expandedSemantic := NOC_ConvLeaves.expand_semantic _ (NOC_Run5bCtx.envOf c)
    expandedValues := NOC_ConvLeaves.expand_values _ (NOC_Run5bCtx.envOf c) l1 l2
    viewed := viewedLib
    observed := hobs }
 exact ⟨_, preparedOk _ _ sem vlib pk pr after hl⟩

#print axioms front
#print axioms preparedOk
#print axioms prepare
end AspisR1.NOC_PrepareConv
end
