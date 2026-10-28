import NDO_JGe_Boundaries
import NDO_JGe_TerminalCondition
import NDO_JGe_Gate
import NDO_JGe_Decode26
import NDO_JGe_RootCalls
set_option autoImplicit false
namespace AspisR1.JHl_SemanticFields
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisS1NativeCompact AspisS1ValuesOwnedInstallation AspisS1ExtractedRoundChildren
open AspisV8R19.SqueezeOracleBridge
attribute [local irreducible] JFx_NativeBytes.proof

theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash)
    (hash : Hash) (identified : JGe_TerminalCondition.Identified) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ (expanded : Slice U8) (pre : r1_wire.Prefix) (sem : r1_semantic.Verified Hash),
      compact.expand_semantic nativeValues JFw_RealExpansion.stored JFw_RealExpansion.initial=ok (.Ok (),expanded) ∧
      PrefixAdapter.parseAccepted expanded=ok (.Ok pre) ∧
      FinishModel.finish children JGe_Boundaries.value D0 JFs_PublicSerialization.value pre
        (⟨encodeState JFm_Q14Source.ratchet,hash,15#u8⟩ : r1_wire.SemanticTranscript Hash)
        JFm_Begin.challenges none=ok (.Ok sem) ∧
      sem.roots=Array.make 2#usize [JFp_InitBytes.root,JFq_Root1.value] ∧
      sem.transcript.state=encodeState JFu_Q26Source.ratchet ∧
      sem.alpha=JFm_PartialAlpha.a10 ∧ sem.z=Array.make 2#usize [JFu_CircleExact.z0,JFu_CircleExact.z1] := by
  obtain ⟨expanded,y1,pre,view,claims,cs,mask,old,same,decode,gather16,gather10,maskCall,maskCanon⟩ :=
    JFu_FinishInputs.inhabited D JGe_Boundaries.value hash
  obtain ⟨expand,parse,yexpand,length,wide,claim,initial,begin,rounds,trace,rows,values,frames,
    read25,circle25,read26,circle26,ineq,canon0,canon1⟩ := old
  have claimsCall := JFu_Claims.source expanded pre expand parse
  have root := JGe_RootCalls.payload pre (JFr_PrefixRecords.source expanded pre expand parse)
  have first := JFp_PrefixRoot.source expanded pre expand parse
  obtain ⟨before,decoded26⟩ := JGe_Decode26.source
  have dec25 : children.decode 29#usize JFu_Q25Source.record 87#usize=ok (.Ok JFu_ClaimsData.a3) := JFu_ClaimsData.decode3
  have dec26 : children.decode 29#usize JFu_Q26Source.record 0#usize=ok (.Ok before) := decoded26
  have needed := identified
  change FIq_Terminal.terminal JFs_PublicSerialization.value JFu_ClaimsData.claims
    JFm_PartialAlpha.a10 JFm_Begin.challenges=ok (.Ok JGd_NumericData.neededTerminal) at needed
  have ga := JFu_MaskGather.gather16
    (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D))
  have gb := JFu_MaskGather.gather10
    (AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D))
  let sem : r1_semantic.Verified Hash := {
    roots := Array.make 2#usize [pre.c1_root,JFq_Root1.value]
    challenges := JFm_Begin.challenges
    alpha := JFm_PartialAlpha.a10
    claims := JFu_ClaimsData.claims
    extra := JFu_ClaimsData.a3
    before_z1 := before
    state_before_z0 := encodeState JFm_Q24Source.ratchet
    z := Array.make 2#usize [JFu_CircleExact.z0,JFu_CircleExact.z1]
    transcript := ⟨encodeState JFu_Q26Source.ratchet,hash,27#u8⟩ }
  refine ⟨expanded,pre,sem,expand,parse,?_,?_,rfl,rfl,rfl⟩
  · unfold FinishModel.finish
    rw [rounds]
    simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,VerifyPrefix.mark]
    simp only [JGe_Boundaries.value]
    rw [claimsCall]
    simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
    rw [needed]
    simp only [bind_tc_ok,core.result.Result.map_err,core.result.Result.Insts.CoreOpsTry.branch,VerifyPrefix.mark]
    rw [ga,bind_tc_ok,gb,bind_tc_ok]
    have c0 : Array.index_usize JFu_ClaimsData.claims 0#usize=ok JFu_ClaimsData.a0 := rfl
    have g : Array.index_usize JFu_ClaimsData.a0 27#usize=ok JFu_MaskInputs.g := rfl
    erw [c0,bind_tc_ok,g,bind_tc_ok,JGd_MaskSource.source,bind_tc_ok,read25]
    simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
    rw [dec25]
    simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
    erw [JGe_Gate.continuation]
    rw [←JGd_MaskedGate.running_eq]
    have eq : core.cmp.PartialEq.ne.trait_default aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
      JGd_NumericData.running JGd_NumericData.running=ok false := by rfl
    rw [eq,bind_tc_ok]
    simp only [Bool.false_eq_true,if_false,VerifyPrefix.mark,r1_wire.SemanticTranscript.impl.state,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch]
    rw [show F3M_CircleSource.install JGe_Boundaries.value=JGe_Boundaries.value from rfl] at circle25 circle26
    erw [circle25]
    simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
    erw [read26]
    simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
    rw [dec26]
    simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
    erw [circle26]
    simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch,VerifyPrefix.mark]
    rw [ineq,bind_tc_ok]
    simp only [Bool.false_eq_true,if_false]
    rw [root]
    simp (config := {zeta := true,zetaDelta := true}) only [bind_tc_ok,Aeneas.Std.uncurry,core.result.Result.Insts.CoreOpsTry.branch]
    have copied : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8
      (Array.to_slice JFq_Root1.value)=ok (.Ok JFq_Root1.value) := by rfl
    rw [copied,bind_tc_ok]
    simp only [S1SemanticRootCopy.unwrapRoot,bind_tc_ok]
  · change Array.make 2#usize [pre.c1_root,JFq_Root1.value]=_
    rw [first]
#print axioms source
end AspisR1.JHl_SemanticFields
