import FinishCandidateOuterSuccess
import AspisR1S9ProductionPairCutV1.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9FinishActualPairSlotV1
abbrev FW := AspisR1FinishRelationCurrent.aspis_core.field.WideExact
abbrev NW := AspisR1S9ProductionPairCutV1.aspis_core.field.wide_exact.WideExact
abbrev Weights := AspisR1S9ProductionPairCutV1.weights.Weights
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

def toNative (x : FW) : NW :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def fromNative (x : NW) : FW :=
  ⟨⟨⟨x.c0.c0.a,x.c0.c0.b⟩,⟨x.c0.c1.a,x.c0.c1.b⟩⟩,
   ⟨⟨x.c1.c0.a,x.c1.c0.b⟩,⟨x.c1.c1.a,x.c1.c1.b⟩⟩⟩
def toNativeSlice (s : Slice FW) : Slice NW := ⟨s.val.map toNative, by simpa using s.property⟩

def fromNativeError : AspisR1S9ProductionPairCutV1.verifier.Error → AspisR1FinishRelationCurrent.verifier.Error
  | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
  | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
  | .Checkpoint => .Checkpoint | .Allocation => .Allocation

/-- Concrete actual Pair implementation in the existing emitted outer finish
operation slot. This is an explicit coordinate-only adapter, with all native
Pair control flow/allocation retained, not an assumed successful callback. -/
def actualPairSlot (self : Weights) (alpha : Slice FW) (message : Slice U8) (kappa : FW) :
    Result (core.result.Result FW AspisR1FinishRelationCurrent.verifier.Error) := do
  let r ← AspisR1S9ProductionPairCutV1.weights.Weights.pair self (toNativeSlice alpha) message (toNative kappa)
  ok (match r with | .Ok x => .Ok (fromNative x) | .Err e => .Err (fromNativeError e))

def installActualPair {D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps Weights D) : AspisR1FinishRelationCurrent.FinishOps Weights D :=
  {ops with pair := actualPairSlot}

/-- Every successful slot result is supplied by the same actual native Pair
call, including its exact input slice, message, kappa and returned value. -/
theorem actualPairSlot_success (self : Weights) (alpha : Slice FW)
    (message : Slice U8) (kappa out : FW)
    (h : actualPairSlot self alpha message kappa = .ok (.Ok out)) :
    ∃ nativeOut,
      AspisR1S9ProductionPairCutV1.weights.Weights.pair self (toNativeSlice alpha) message (toNative kappa) =
        .ok (.Ok nativeOut) ∧ out = fromNative nativeOut := by
  unfold actualPairSlot at h
  cases hr : AspisR1S9ProductionPairCutV1.weights.Weights.pair self (toNativeSlice alpha) message (toNative kappa) with
  | fail e => simp only [hr,bind_tc_fail] at h; cases h
  | div => simp only [hr,bind_tc_div] at h; cases h
  | ok r =>
    simp only [hr,bind_tc_ok] at h
    cases r with
    | Err e => cases h
    | Ok nativeOut =>
      have he : fromNative nativeOut = out := core.result.Result.Ok.inj (Result.ok.inj h)
      exact ⟨nativeOut,rfl,he.symm⟩

/-- Existing accepted S2 finish control flow now reaches the concrete actual
Pair body on the exact slice returned by its own Array2 RangeTo2 operation.
No separate Pair success or caller/input-equality assumption is supplied.
Other finish operation slots remain explicit, as in the retained outer cut. -/
theorem finish_s2_success_reaches_actual_pair {D : Type} (ops : AspisR1FinishRelationCurrent.FinishOps Weights D)
    (v : AspisR1FinishRelationCurrent.verifier.View) (p : AspisR1FinishRelationCurrent.verifier.Prepared) (a : AspisR1FinishRelationCurrent.verifier.Accumulator)
    (obs : Option (AspisR1FinishRelationCurrent.verifier.Phase → Result Unit))
    (hv : p.variant = AspisR1FinishRelationCurrent.transport.Variant.S2)
    (h : AspisR1FinishRelationCurrent.verifier.finish_relation (installActualPair ops) v p a obs = .ok (.Ok ())) :
    ∃ (self : Weights) (selected : Slice FW) (nativeOut : NW),
      ops.newWeights p.variant p.semantic_alpha p.z = .ok (.Ok self) ∧
      core.array.Array.index (core.ops.index.IndexSlice
        (core.slice.index.SliceIndexRangeToUsizeSlice FW))
        p.alpha { «end» := 2#usize } = .ok selected ∧
      AspisR1S9ProductionPairCutV1.weights.Weights.pair self (toNativeSlice selected) v.final_message (toNative p.kappa) =
        .ok (.Ok nativeOut) := by
  obtain ⟨alpha0,claim1,alpha1,claim2,self,selected,pair,actual,
      hr0,hround0,hr1,hround1,hnew,hselected,hpair,hrest⟩ :=
    AspisR1FinishRelationCurrent.FinishCandidateOuterSuccess.s2_success_calls (installActualPair ops) v p a obs hv h
  obtain ⟨nativeOut,hnative,hout⟩ := actualPairSlot_success self selected v.final_message p.kappa pair hpair
  exact ⟨self,selected,nativeOut,hnew,hselected,hnative⟩

#print axioms actualPairSlot_success
#print axioms finish_s2_success_reaches_actual_pair
end AspisR1S9FinishActualPairSlotV1
