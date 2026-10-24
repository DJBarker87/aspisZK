import Port4B_CallerJoin

set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4B_FoldedCut
open Aeneas Aeneas.Std Result VTop_Stages
open MultiproofConeCanonical MultiproofConeSlices
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

def unwrap32 (r : core.result.Result (Array U8 32#usize) core.array.TryFromSliceError) : Result (Array U8 32#usize) :=
  match r with | .Ok a => ok a | .Err _ => fail .panic

/-- Exact current native folded-root constants and copy/unwrap leaf. -/
def install (base : Ops) : Ops :=
  {base with op5:=Port4B_Install.batch,op14:=ok 7783#usize,op15:=ok 7751#usize,unwrap32:=unwrap32}

theorem tx1 (base : Ops) {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (accepted : verifier.candidate.tx1 (install base) D semantic pub proof split hash none=ok (.Ok saved)) :
    ∃ p root view,
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7751#usize,«end»:=7783#usize}=ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root) ∧
      Port4B_Install.batch D proof p root 0#usize hash=ok (.Ok ()) := by
  unfold verifier.candidate.tx1 at accepted
  simp only [install] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals exact ⟨_,_,_,by assumption,by assumption,by assumption⟩

theorem tx2 (base : Ops) {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (pub proof checkpoint : Slice U8)
    (accepted : verifier.candidate.tx2_authenticated (install base) D pub proof checkpoint hash none=ok (.Ok ())) :
    ∃ p a root view,
      base.op18 D checkpoint proof pub .S2 hash=ok (.Ok (p,a)) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7751#usize,«end»:=7783#usize}=ok view ∧
      core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root) ∧
      Port4B_Install.batch D proof p root 1#usize hash=ok (.Ok ()) := by
  unfold verifier.candidate.tx2_authenticated verifier.candidate.tx2_common at accepted
  simp only [install] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals exact ⟨_,_,_,_,by assumption,by assumption,by assumption,by assumption⟩

theorem bytes (proof view : Slice U8) (root : Array U8 32#usize) (len : proof.val.length=57607)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7751#usize,«end»:=7783#usize}=ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root)) :
    bytesOf root.val=OraclePortCompactDraft.slice (bytesOf proof.val) 7751 32 := by
  obtain ⟨r,call,fields⟩ := WP.spec_imp_exists (core.array.TryFromArrayCopySlice.try_from.step 32#usize core.marker.CopyU8 view)
  have same := Result.ok.inj (call.symm.trans copy)
  subst r
  have actual := range_total proof 7751#usize 7783#usize (by decide) (by change 7783≤proof.val.length;omega)
  have viewEq := Result.ok.inj (range.symm.trans actual)
  rw [fields.1,viewEq,bytes_sub]
  rfl

/-- The model folded-root input is derived from this exact physical copy,
without a hash equality, alternate allocation or successful second read. -/
theorem model (proof view : Slice U8) (root : Array U8 32#usize) (len : proof.val.length=57607)
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire=bytesOf proof.val)
    (range : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      proof {start:=7751#usize,«end»:=7783#usize}=ok view)
    (copy : core.array.TryFromArrayCopySlice.try_from 32#usize core.marker.CopyU8 view=ok (.Ok root)) :
    bytesOf root.val=AspisV8R19.SourceDuplexStep.bytes (OraclePortBatchDraft.committedRoot parsed 2) := by
  have physical := bytes proof view root len range copy
  have encoded := MultiproofConePhysicalTransport.digest_bytes root
  have source : OraclePortCompactDraft.root2 parsed=AspisV8R19.SourceDuplexStep.bytes (decodeState root) := by
    simpa only [OraclePortCompactDraft.root2,wire] using physical.symm.trans encoded.symm
  simp only [OraclePortBatchDraft.committedRoot,show ¬(2:Nat)=0 by decide,show ¬(2:Nat)=1 by decide,
    if_false,source,SemanticRecordCodec.decodeState_bytes,Option.getD_some]
  exact encoded.symm

#print axioms tx1
#print axioms tx2
#print axioms bytes
#print axioms model
end AspisR1.Port4B_FoldedCut
end
