import NOC_Run5bHost
import NNH_SliceRangeOk
import NNV_PreparedFront
import NNV_PrepareView
import NNV_PrepareValuesOutput
import NNV_PrepareSemanticOutput
import NNV_PrepareFilled
import NNH_Run5bCurrentExpand
import NNG_Split087
import NOC_PrepareDiv
import NNX_PreparedValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NOC_PrepareFront
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NOC_FinishSource

abbrev cur {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :=
 DrvC_Installation.currentInstalled (NOC_Run5bCtx.configuration c)

def zeros (n : Usize) : alloc.vec.Vec U8 :=
 ⟨List.replicate n.val 0#u8,by simp only [List.length_replicate]; scalar_tac⟩

/-- The corrected allocation slot on a granted reservation. -/
theorem filled {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) (n : Usize)
 (granted : (NNH_HostCtx.envOf c).reservation = true) :
 (cur c).op1 core.marker.CopyU8 n 0#u8 = ok (.Ok (zeros n)) := by
 change NOC_HostSeed.filled (NNH_HostCtx.envOf c).reservation core.marker.CopyU8 n 0#u8 = _
 unfold NOC_HostSeed.filled
 rw [LIBC_Filled.model n (NNH_HostCtx.envOf c),granted]
 rfl

theorem logical_semantic {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 compact.LOGICAL_SEMANTIC (cur c) = ok 13831#usize := by
 unfold compact.LOGICAL_SEMANTIC; rfl
theorem off_semantic {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 compact.OFF_SEMANTIC (cur c) = ok 16#usize := by
 unfold compact.OFF_SEMANTIC; rfl
theorem off_y1 {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 compact.OFF_Y1 (cur c) = ok 7031#usize := by
 unfold compact.OFF_Y1 compact.OFF_SEMANTIC
 change (do let i ← ok 16#usize; let i1 ← ok 7015#usize; i + i1) = ok 7031#usize
 simp only [bind_tc_ok]
 apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac
theorem off_inactive {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx) :
 compact.OFF_INACTIVE (cur c) = ok 7495#usize := by
 unfold compact.OFF_INACTIVE
 rw [off_y1]
 change (do let i ← ok 7031#usize; let i1 ← ok 464#usize; i + i1) = ok 7495#usize
 simp only [bind_tc_ok]
 apply AspisR1CurrentCaller.UsizeArithmetic.add_eq_ok <;> scalar_tac

theorem bytes_length (s : Slice U8) : (LIB_Carriers.bytes s).length = s.val.length := by
 simp only [LIB_Carriers.bytes,NMS_R2N_RSLScalars.bytes,List.length_map]

/-- A checked proof window is the RSL slice of the SAME proof bytes. -/
theorem window (proof : Slice U8) (width : proof.val.length = 57607) (start stop : Usize)
 (a b : Nat) (ha : start.val = a) (hb : stop.val = b) (hab : a ≤ b) (hb57 : b ≤ 57607) :
 ∃ out, core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) proof
   {start := start, «end» := stop} = ok out ∧
  out = LIBC_Bytes.raw (RSL.slice (LIB_Carriers.bytes proof) a b) ∧
  out.val.length = b - a := by
 obtain ⟨out,run,same⟩ := NNH_SliceRangeOk.value proof start stop (by scalar_tac)
  (by change stop.val ≤ proof.val.length; omega)
 have same' : LIB_Carriers.bytes out = RSL.slice (LIB_Carriers.bytes proof) a b := by
  rw [← ha,← hb]; exact same
 have raw : out = LIBC_Bytes.raw (RSL.slice (LIB_Carriers.bytes proof) a b) :=
  (LIBC_Bytes.from_native out).symm.trans (congrArg LIBC_Bytes.raw same')
 refine ⟨out,run,raw,?_⟩
 have l := congrArg List.length same'
 rw [bytes_length] at l
 rw [l]
 simp only [RSL.slice,List.length_take,List.length_drop,bytes_length,width]
 omega

/-- The values expansion output depends on its destination only by length. -/
theorem values_congr (src b1 b2 : Slice U8) (same : b1.val.length = b2.val.length) :
 LIBC_ExpandValuesModel.output src b1 = LIBC_ExpandValuesModel.output src b2 := by
 apply Subtype.ext
 apply List.ext_getElem
 · simp only [LIBC_ExpandValuesModel.output,List.length_ofFn,same]
 · intro j h1 h2
   simp only [LIBC_ExpandValuesModel.output,List.getElem_ofFn]

/-- Installed owned values expansion equals the closed LIBC model (same
argument as NGV_ExpandAssociation.result, restated without its import). -/
theorem values (src before : Slice U8) (n16 : src.val.length % 16 = 0)
 (shape : before.val.length = 2 * src.val.length) (bound : src.val.length ≤ 1856) :
 AspisS1ValuesOwnedInstallation.expandValues src before =
 ok (.Ok (),LIBC_ExpandValuesModel.output src before) := by
 obtain ⟨native,nativeRun,nativeLength,nativeBytes⟩ := NGV_ExpandPacket.result src before bound n16 shape
 obtain ⟨model,modelRun,modelLength,modelBytes⟩ := AspisS1ValuesOwnedExact.installed_exact
  src before n16 shape (by scalar_tac)
 have closed := LIBC_ExpandValuesModel.source src before bound
 rw [if_pos ⟨n16,shape⟩] at closed
 have nativeIs : native = LIBC_ExpandValuesModel.output src before :=
  congrArg Prod.snd (Result.ok.inj (nativeRun.symm.trans closed))
 have same : native = model := by
  apply Subtype.ext
  apply List.ext_getElem
  · exact nativeLength.trans modelLength.symm
  · intro j hj hk
    have hn := nativeBytes j (by omega)
    have hm := congrArg (fun x : Option U8 => x.getD 0#u8) (modelBytes j hk)
    have eq : native.val[j]?.getD 0#u8 = model.val[j]?.getD 0#u8 := by
     rw [hn,hm]
     unfold NFU_Retarget.LPl_A.Expand.byte
     split <;> rfl
    simpa only [List.getElem?_eq_getElem hj,List.getElem?_eq_getElem hk,Option.getD_some] using eq
 rw [modelRun,← same,nativeIs]

theorem recombined (a b : Slice U8) (ha : a.val.length = 13831) (v : alloc.vec.Vec U8)
 (hv : v.val = a.val ++ b.val) :
 alloc.vec.Vec.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) v {«end» := 13831#usize} = ok a ∧
 alloc.vec.Vec.index (core.slice.index.SliceIndexRangeFromUsizeSlice U8) v {start := 13831#usize} = ok b := by
 have hlen : (13831#usize).val ≤ v.val.length := by
  rw [hv,List.length_append,ha]; scalar_tac
 have hc : a.val.length = (13831#usize).val := by rw [ha]; scalar_tac
 refine ⟨NHL_BorrowWindows.left v a 13831#usize hlen ?_,NHL_BorrowWindows.right v b 13831#usize hlen ?_⟩
 · rw [hv]; first | exact List.take_left' hc | simp [hc]
 · rw [hv]; first | exact List.drop_left' hc | simp [hc]

/-- X4 at the corrected configuration: the SAME canonical returned prepare
(library 087) is the installed prepare front's full Result, including scratch.
`width` is the 57607-byte proof domain that the 094 path establishes. -/
theorem source {W Tx : Type} (c : NNH_HostCtx.Ctx W Tx)
 (pub : NNH_Libraries.VL.Public) (proof : Slice U8) (g g' : LIB_VCarriers.E29)
 (prep : LIB_VCarriers.Prepared) (width : proof.val.length = 57607)
 (called : NNH_Tx1Returns.preparedValue ⟨pub,LIB_Carriers.bytes proof,g⟩ (NOC_Run5bCtx.envOf c) =
  .ok (prep,g')) :
 verifier.candidate.prepare (cur c) (NNV_PreparedAtHost.digest c)
  (FirstComposition.toCurrentPublic pub) proof () none (NNV_PreparedInputs.scratch g) =
 .ok (.Ok (InstalledPreparation.currentPrepared prep),NNV_PreparedInputs.scratch g') := by
 obtain ⟨sem,v,⟨pk⟩,prepCalled⟩ := NNV_PreparedFront.returned _ _ prep g' called
 have filledFacts := NNV_PrepareFilled.returned _ _ sem v pk
 have granted : (NNH_HostCtx.envOf c).reservation = true := filledFacts.1
 have semLib : pk.semantic = LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output
   (LIBC_Bytes.raw (RSL.slice (LIB_Carriers.bytes proof) 16 7031))) :=
  NNV_PrepareSemanticOutput.returned _ _ sem v pk
 have valLib := NNV_PrepareValuesOutput.returned _ _ sem v pk
 have y1Lib : pk.y1 = LIB_Carriers.bytes (LIBC_ExpandValuesModel.output
   (LIBC_Bytes.raw (RSL.slice (LIB_Carriers.bytes proof) 7031 7495))
   (LIBC_Bytes.raw (pk.logical.drop 13831))) := valLib.2
 -- native windows
 obtain ⟨s1,s1Run,s1Raw,s1Len⟩ := window proof width 16#usize 7031#usize 16 7031
  (by scalar_tac) (by scalar_tac) (by decide) (by decide)
 obtain ⟨s2,s2Run,s2Raw,s2Len⟩ := window proof width 7031#usize 7495#usize 7031 7495
  (by scalar_tac) (by scalar_tac) (by decide) (by decide)
 -- split of the zero buffer
 obtain ⟨left,right,back,splitRun,leftVal,rightVal,backVal⟩ :=
  NNG_Split087.split (alloc.vec.Vec.deref_mut (zeros 14759#usize)).1 13831#usize
   (by simp only [zeros,alloc.vec.Vec.deref_mut,List.length_replicate]; scalar_tac)
 have leftLen : left.val.length = 13831 := by
  rw [leftVal]; simp only [zeros,alloc.vec.Vec.deref_mut,List.length_take,List.length_replicate]; scalar_tac
 have rightLen : right.val.length = 928 := by
  rw [rightVal]; simp only [zeros,alloc.vec.Vec.deref_mut,List.length_drop,List.length_replicate]; scalar_tac
 have s1L : s1.val.length = 7015 := s1Len
 have s2L : s2.val.length = 464 := s2Len
 have expS := NNH_Run5bCurrentExpand.semantic (NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation)
  (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation s1 left s1L leftLen
 have expV : (cur c).op11 s2 right = ok (.Ok (),LIBC_ExpandValuesModel.output s2 right) :=
  values s2 right (by rw [s2L]) (by rw [s2L,rightLen]) (by rw [s2L]; decide)
 have semOutLen : (LIBC_ExpandSemanticModel.output s1).val.length = 13831 := by
  have := NNV_PrepareSemanticOutput.length _ _ sem v pk
  rw [semLib,bytes_length,← s1Raw] at this
  exact this
 have valOutLen : (LIBC_ExpandValuesModel.output s2 right).val.length = 928 := by
  simp only [LIBC_ExpandValuesModel.output,List.length_ofFn,rightLen]
 have vecVal : ((alloc.vec.Vec.deref_mut (zeros 14759#usize)).2
   (back (LIBC_ExpandSemanticModel.output s1,LIBC_ExpandValuesModel.output s2 right))).val =
   (LIBC_ExpandSemanticModel.output s1).val ++ (LIBC_ExpandValuesModel.output s2 right).val :=
  backVal _ _ (by rw [semOutLen,leftLen]) (by rw [valOutLen,rightLen])
 have windows := recombined _ _ semOutLen _ vecVal
 -- library bytes of the two native halves
 have semBytes : LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output s1) = pk.semantic := by
  rw [semLib,← s1Raw]
 have logical : pk.logical.drop 13831 = List.replicate 928 (0 : UInt8) := by
  rw [filledFacts.2]
  show List.drop 13831 (List.replicate (13831+928) (0 : UInt8)) = List.replicate 928 0
  rw [List.drop_replicate,Nat.add_sub_cancel_left]
 have rightRaw : right.val.length = (LIBC_Bytes.raw (pk.logical.drop 13831)).val.length := by
  rw [rightLen,logical,LIBC_Bytes.raw_length _ (by simp only [List.length_replicate]; scalar_tac)]
  all_goals simp only [List.length_replicate]
 have valBytes : LIB_Carriers.bytes (LIBC_ExpandValuesModel.output s2 right) = pk.y1 := by
  rw [y1Lib,← s2Raw]
  exact congrArg LIB_Carriers.bytes (values_congr s2 right _ rightRaw)
 have viewed : LIB_VLib.wideViewValue (LIB_Carriers.bytes proof,
   LIB_Carriers.bytes (LIBC_ExpandSemanticModel.output s1),
   LIB_Carriers.bytes (LIBC_ExpandValuesModel.output s2 right)) (NNH_HostCtx.envOf c) = .ok v := by
  rw [semBytes,valBytes]; exact pk.viewed
 have view := NNV_PrepareView.returned (NOC_HostSeed.m0 (NNH_HostCtx.envOf c).reservation)
  (NNH_HostCtx.envOf c) c.fixed.indexError c.fixed.reservation proof _ _ v width semOutLen valOutLen viewed
 have semCall := NOC_SeedTransfer.op9 c pub (NNV_PreparedInputs.view v).semantic sem pk.observed
 have prepCall := NNX_PreparedValue.source c sem v g g' prep prepCalled
 unfold verifier.candidate.prepare
 noc_stp (logical_semantic c)
 noc_stp (AspisR1.NOC_PrepareDiv.logical_y1)
 noc_stp (AspisR1.NOC_PrepareDiv.logical_sum)
 noc_stp (filled c 14759#usize granted)
 noc_stp rfl
 noc_nrm
 noc_stp rfl
 noc_nrm
 noc_stp splitRun
 noc_nrm
 noc_stp (off_semantic c)
 noc_stp (off_y1 c)
 noc_stp s1Run
 noc_stp expS
 noc_nrm
 noc_stp (off_inactive c)
 noc_stp s2Run
 noc_stp expV
 noc_nrm
 noc_stp windows.1
 noc_stp windows.2
 noc_stp view
 noc_nrm
 noc_stp semCall
 noc_stp rfl
 noc_nrm
 noc_stp rfl
 exact prepCall
#print axioms filled
#print axioms off_y1
#print axioms off_inactive
#print axioms window
#print axioms values_congr
#print axioms values
#print axioms recombined
#print axioms source
end AspisR1.NOC_PrepareFront
end
