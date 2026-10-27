import RPz7_S1NativePrepareBuffersV1
import ExtractedPrefixParse
set_option autoImplicit false
namespace AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open OriginalSerializerInstallation

private theorem stored_range (proof stored : Slice U8)
    (call : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=16#usize,«end»:=7031#usize}=ok stored) :
    7031≤proof.val.length ∧ stored.val=proof.val.slice 16 7031 := by
  simp only [Slice.index_SliceIndexRangeUsizeSliceInst] at call
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index at call
  split at call
  · rename_i bounds
    have same := Result.ok.inj call
    have bytes := congrArg (fun s : Slice U8 => s.val) same
    exact ⟨by scalar_tac,bytes.symm⟩
  · cases call

private theorem physical_prefix (proof stored expanded : Slice U8) (root : Array U8 32#usize)
    (storedCall : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=16#usize,«end»:=7031#usize}=ok stored)
    (kept : AspisS1NativeCompactBodyFrame.Prefix 32 stored expanded)
    (rootBytes : root.val=expanded.val.take 32) : root.val=proof.val.slice 16 48 := by
  obtain ⟨proofBound,storedBytes⟩ := stored_range proof stored storedCall
  apply List.ext_getElem?
  intro j
  by_cases hj : j<32
  · rw [rootBytes]
    calc
      (expanded.val.take 32)[j]?=expanded.val[j]? := List.getElem?_take_of_lt hj
      _=stored.val[j]? := kept j hj
      _=proof.val[16+j]? := by
        rw [storedBytes]
        exact List.getElem?_slice 16 7031 j proof.val (by omega)
      _=(proof.val.slice 16 48)[j]? :=
        (List.getElem?_slice 16 48 j proof.val (by omega)).symm
  · have rootLength : root.val.length=32 := by simpa using root.property
    have physicalLength : (proof.val.slice 16 48).length=32 := by
      rw [List.slice_length]
      omega
    have leftNone : root.val[j]?=none := by simp only [List.getElem?_eq_none_iff];omega
    have rightNone : (proof.val.slice 16 48)[j]?=none := by
      simp only [List.getElem?_eq_none_iff];omega
    exact leftNone.trans rightNone.symm

/-- First Prepared root is the physical proof's bytes 16..48 on this SAME
complete source preparation return. The actual native semantic expansion,
buffer reconstruction, View and parser are connected. The Y1 value-expansion
length law remains explicit; no root, parser, expansion or child-success
premise is supplied independently. This does not close the second root or
full source/security refinement. -/
theorem prepare_physical_root0 (ops : Ops) (native : AspisS1NativeCompact.Ops)
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
      prepared.roots=Array.make 2#usize [root0,root1] ∧ root0.val=proof.val.slice 16 48 := by
  obtain ⟨stored,initial,expanded,y1,view,sem,hstored,hexpanded,hview,hviewSemantic,hsem,hnew⟩ :=
    prepare_buffers ops native R B valueLength D pub proof hash prepared input scratch success
  have fields := originalNew_static (withOriginalSerializer closedSampling) AspisS1M31Embedding.Total.embed
    D sem view hash prepared scratch input hnew
  obtain ⟨pre,initialTranscript,after,challenges,payload,root1,parsed,
    publicInit,begin,finish,hpayload,hcopy,hpayloadBytes,hroots⟩ :=
    S1SemanticInstallation.verify_roots R B D pub expanded hash sem hsem
  have nativePrefix := AspisS1NativeCompactBodyFrame.semantic_root_prefix
    native stored initial expanded hexpanded
  have parser := AspisR1PublicPreparation.PrefixAdapter.parse_success expanded pre parsed
  have rootBytes := (AspisR1.ExtractedPrefixParse.parse_success expanded
    (AspisR1PublicPreparation.PrefixAdapter.toOld pre) parser).1
  change pre.c1_root.val=expanded.val.take 32 at rootBytes
  exact ⟨pre.c1_root,root1,fields.2.1.trans hroots,
    physical_prefix proof stored expanded pre.c1_root hstored nativePrefix rootBytes⟩

#print axioms prepare_physical_root0
end AspisR1CurrentCaller.BorrowedClaimPrepared.NativeBuffers
