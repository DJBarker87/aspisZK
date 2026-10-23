import S9FinishActualPairSlotV1
import S9ResumeAlphaPairInputV1
import S9CandidateFoldMapPrimitivesV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ResumeFinishNativePairBindingV1
abbrev SW := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
abbrev FW := AspisR1S9FinishActualPairSlotV1.FW
abbrev NW := AspisR1S9FinishActualPairSlotV1.NW
abbrev Weights := AspisR1S9FinishActualPairSlotV1.Weights
abbrev mapArray := @AspisR1S9CandidateFoldMapPrimitivesV1.mapArray
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def stageVariant : AspisR1Stage2.transport.Variant → AspisR1FinishRelationCurrent.transport.Variant
  | .S1 => .S1 | .S2 => .S2 | .D => .D

def stageQM (x : AspisR1Stage2.aspis_core.field.QM31) : AspisR1FinishRelationCurrent.aspis_core.field.QM31 :=
  ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def stageWide (x : SW) : FW := ⟨stageQM x.c0,stageQM x.c1⟩
def stagePoint (x : AspisR1Stage2.aspis_core.circle.SecureCirclePoint) :
    AspisR1FinishRelationCurrent.aspis_core.circle.SecureCirclePoint := ⟨stageQM x.x,stageQM x.y⟩

/-- Complete Prepared carrier transport: every source field is retained.
Only nominal record owners change; no field operation or transcript step. -/
def stagePrepared (p : AspisR1Stage2.verifier.Prepared) : AspisR1FinishRelationCurrent.verifier.Prepared :=
  {variant := stageVariant p.variant, roots := p.roots,
   gamma := stageWide p.gamma, kappa := stageWide p.kappa,
   alpha := mapArray stageWide p.alpha, rho := stageQM p.rho, queries := p.queries,
   semantic_alpha := mapArray stageQM p.semantic_alpha, z := mapArray stagePoint p.z,
   claim := stageWide p.claim, state := p.state}

theorem same_native_alpha_prefix (p : AspisR1Stage2.verifier.Prepared) (selected : Slice FW)
    (hselected : core.array.Array.index (core.ops.index.IndexSlice
      (core.slice.index.SliceIndexRangeToUsizeSlice FW))
      (stagePrepared p).alpha { «end» := 2#usize } = .ok selected) :
    AspisR1S9FinishActualPairSlotV1.toNativeSlice selected =
      AspisR1S9ResumeAlphaPairInputV1.toNativeSlice (Array.to_slice p.alpha) := by
  rw [AspisR1S9ArrayTwoPrefixSourceV1.successful_array_two_prefix_eq
    (stagePrepared p).alpha selected hselected]
  apply Subtype.ext
  change (p.alpha.val.map stageWide).map AspisR1S9FinishActualPairSlotV1.toNative =
    p.alpha.val.map AspisR1S9ResumeAlphaPairInputV1.toNative
  rw [List.map_map]
  rfl

/-- An accepted finish call on the concrete carrier transport of the SAME
strict resume output reaches actual native Pair on that exact alpha slice.
Neither successful prefix/Pair child calls nor input canonicality is assumed.
Other existing finish slots and runtime/caller installation remain explicit. -/
theorem resume_finish_success_reaches_canonical_actual_pair {D H : Type}
    (readerOps : AspisR1Stage2.ResumeOps)
    (digest : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (bytes proof publicInput : Slice U8) (hash : H)
    (p : AspisR1Stage2.verifier.Prepared) (acc : AspisR1Stage2.verifier.Accumulator)
    (ops : AspisR1FinishRelationCurrent.FinishOps Weights D)
    (v : AspisR1FinishRelationCurrent.verifier.View)
    (a : AspisR1FinishRelationCurrent.verifier.Accumulator)
    (obs : Option (AspisR1FinishRelationCurrent.verifier.Phase → Result Unit))
    (hresume : AspisR1Stage2.verifier.resumeWithOps
      (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE readerOps)
      digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash = .ok (.Ok (p,acc)))
    (hfinish : AspisR1FinishRelationCurrent.verifier.finish_relation
      (AspisR1S9FinishActualPairSlotV1.installActualPair ops)
      v (stagePrepared p) a obs = .ok (.Ok ())) :
    ∃ (self : Weights) (selected : Slice FW) (nativeOut : NW),
      ops.newWeights (stagePrepared p).variant (stagePrepared p).semantic_alpha
        (stagePrepared p).z = .ok (.Ok self) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice FW))
        (stagePrepared p).alpha { «end» := 2#usize } = .ok selected ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.pair self
        (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) v.final_message
        (AspisR1S9FinishActualPairSlotV1.toNative (stagePrepared p).kappa) = .ok (.Ok nativeOut) ∧
      ∀ (i : Usize) (value : NW), Slice.index_usize
        (AspisR1S9FinishActualPairSlotV1.toNativeSlice selected) i = .ok value →
        AspisR1S9ActualPairWideCanonicalV1.Canonical value := by
  obtain ⟨fields⟩ := AspisR1.OraclePortCkptAbiSourceFields.successful_fields
    (AspisR1S4ResumeGammaActualCanonicalV1.withReaderE readerOps)
    digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash p acc hresume
  have hv : (stagePrepared p).variant = AspisR1FinishRelationCurrent.transport.Variant.S2 := by
    change stageVariant p.variant = _
    rw [fields.variant]
    rfl
  obtain ⟨self,selected,nativeOut,hnew,hselected,hpair⟩ :=
    AspisR1S9FinishActualPairSlotV1.finish_s2_success_reaches_actual_pair
      ops v (stagePrepared p) a obs hv hfinish
  refine ⟨self,selected,nativeOut,hnew,hselected,hpair,?_⟩
  have hc := AspisR1S9ResumeAlphaPairInputV1.resume_finish_prefix_native_alpha_canonical
    readerOps digest bytes proof publicInput AspisR1Stage2.transport.Variant.S2 hash p acc
    (Array.to_slice p.alpha) hresume
    (AspisR1S9ArrayTwoPrefixSourceV1.array_two_prefix_exact p.alpha)
  intro i value hread
  apply hc i value
  rw [← same_native_alpha_prefix p selected hselected]
  exact hread

#print axioms same_native_alpha_prefix
#print axioms resume_finish_success_reaches_canonical_actual_pair
end AspisR1S9ResumeFinishNativePairBindingV1
