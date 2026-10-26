import S1ParsedSecondRootBytesV1
import S1NativeCompactPrefix79V1
import S1AcceptedSliceRangeV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open OriginalSerializerInstallation

private theorem physical_second_segment (proof stored expanded : Slice U8)
    (call : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=16#usize,«end»:=7031#usize}=ok stored)
    (kept : AspisS1NativeCompactBodyFrame.Prefix 79 stored expanded) :
    expanded.val.slice 47 79=proof.val.slice 63 95 := by
  obtain ⟨ordered,bound,storedLength⟩ :=
    AspisS1AcceptedSliceRange.accepted_range proof stored 16#usize 7031#usize call
  have proofBound : 7031≤proof.val.length := by scalar_tac
  have storedSize : stored.val.length=7015 := by scalar_tac
  obtain ⟨value,sourceCall,sourceFacts⟩ := WP.spec_imp_exists
    (core.slice.index.SliceIndexRangeUsizeSlice.index.step_spec
      {start:=16#usize,«end»:=7031#usize} proof ordered bound)
  have same : value=stored := Result.ok.inj (sourceCall.symm.trans call)
  subst value
  have sourceBytes : stored.val=proof.val.slice 16 7031 := by
    simpa only [show (16#usize : Usize).val=16 by scalar_tac,
      show (7031#usize : Usize).val=7031 by scalar_tac] using sourceFacts.1
  have expandedBound : 79≤expanded.val.length := by
    by_contra short
    have absent : expanded.val[78]?=none := List.getElem?_eq_none_iff.mpr (by omega)
    have storedAbsent : stored.val[78]?=none := (kept 78 (by decide)).symm.trans absent
    have impossible := List.getElem?_eq_none_iff.mp storedAbsent
    omega
  apply List.ext_getElem?
  intro j
  by_cases hj : j<32
  · calc
      (expanded.val.slice 47 79)[j]?=expanded.val[47+j]? :=
        List.getElem?_slice 47 79 j expanded.val (by omega)
      _=stored.val[47+j]? := kept (47+j) (by omega)
      _=proof.val[63+j]? := by
        rw [sourceBytes]
        have byte := List.getElem?_slice 16 7031 (47+j) proof.val (by omega)
        have address : 16+(47+j)=63+j := by omega
        simpa only [address] using byte
      _=(proof.val.slice 63 95)[j]? :=
        (List.getElem?_slice 63 95 j proof.val (by omega)).symm
  · have leftLength : (expanded.val.slice 47 79).length=32 := by rw [List.slice_length];omega
    have rightLength : (proof.val.slice 63 95).length=32 := by rw [List.slice_length];omega
    have leftNone : (expanded.val.slice 47 79)[j]?=none := by
      simp only [List.getElem?_eq_none_iff];omega
    have rightNone : (proof.val.slice 63 95)[j]?=none := by
      simp only [List.getElem?_eq_none_iff];omega
    exact leftNone.trans rightNone.symm

/-- BOTH Prepared roots are physical proof bytes, derived from one full
preparation with actual native expansion, buffer reconstruction and parser.
No desired root identity or successful intermediate call is a premise.
The explicit Y1 length law, native leaf/SDK and other S1 gates remain open. -/
theorem prepare_physical_roots (ops : Ops) (native : AspisS1NativeCompact.Ops)
    (R : AspisR1PublicPreparation.RoundModel.Boundaries)
    (B : AspisR1PublicPreparation.FinishModel.Boundaries)
    (valueLength : ∀ input output status updated,
      ops.op11 input output=ok (status,updated) → updated.length=output.length)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (prepared : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (success : verifier.candidate.prepare (install ops native R B)
      D pub proof hash none input=ok (.Ok prepared,scratch)) :
    ∃ (root0 root1 : Array U8 32#usize),
      prepared.roots=Array.make 2#usize [root0,root1] ∧
      root0.val=proof.val.slice 16 48 ∧ root1.val=proof.val.slice 63 95 := by
  obtain ⟨root0,root1,oldRoots,physical0⟩ :=
    prepare_physical_root0 ops native R B valueLength D pub proof hash prepared input scratch success
  obtain ⟨stored,initial,expanded,y1,view,sem,hstored,hexpanded,hview,hviewSemantic,hsem,hnew⟩ :=
    prepare_buffers ops native R B valueLength D pub proof hash prepared input scratch success
  have fields := originalNew_static (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
    D sem view hash prepared scratch input hnew
  obtain ⟨pre,initialTranscript,after,challenges,payload,second,parsed,
    publicInit,begin,finish,hpayload,hcopy,hpayloadBytes,hroots⟩ :=
    S1SemanticInstallation.verify_roots R B D pub expanded hash sem hsem
  have payloadBytes := AspisS1ParsedSecondRootBytes.row2_bytes expanded pre payload parsed hpayload
  have nativePrefix := AspisS1NativeCompactPrefix79.semantic_prefix79 native stored initial expanded hexpanded
  have physical1 : second.val=proof.val.slice 63 95 :=
    hpayloadBytes.trans (payloadBytes.trans (physical_second_segment proof stored expanded hstored nativePrefix))
  have newRoots : prepared.roots=Array.make 2#usize [pre.c1_root,second] := fields.2.1.trans hroots
  have identities := congrArg (fun a : Array (Array U8 32#usize) 2#usize => a.val)
    (newRoots.symm.trans oldRoots)
  change [pre.c1_root,second]=[root0,root1] at identities
  have sameSecond : second=root1 := (List.cons.inj (List.cons.inj identities).2).1
  exact ⟨root0,root1,oldRoots,physical0,by rw [←sameSecond];exact physical1⟩

#print axioms prepare_physical_roots
end AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers
