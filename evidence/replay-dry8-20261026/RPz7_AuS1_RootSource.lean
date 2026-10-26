import RPz7_AuS1_Offsets
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_RootSource
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation
open MultiproofConeCanonical MultiproofConeSlices
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.SqueezeOracleBridge

 theorem root (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1 = ok (.Ok view)) :
    ∃ (root : Array U8 32#usize) (part : Slice U8),
      view.folded_root = some root ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7751#usize,«end»:=7783#usize} = ok part ∧ root.val = part.val := by
  obtain ⟨root,start,finish,part,field,hs,hf,range,contents⟩ := AuS1_ViewSource.folded proof semantic y1 view accepted
  have startEq : start = 7751#usize := (Result.ok.inj (AuS1_Offsets.folded.symm.trans hs)).symm
  have finishEq : finish = 7783#usize := (Result.ok.inj (AuS1_Offsets.round1.symm.trans hf)).symm
  subst start
  subst finish
  exact ⟨root,part,field,range,contents⟩

 theorem model (proof semantic y1 : Slice U8) (view : verifier.View)
    (accepted : sourceView proof semantic y1 = ok (.Ok view))
    (parsed : OraclePortCompactDraft.Parsed) (wire : parsed.wire = bytesOf proof.val) :
    ∃ root : Array U8 32#usize,
      view.folded_root = some root ∧
      decodeState root = OraclePortBatchDraft.committedRoot parsed 2 := by
  obtain ⟨root,part,field,range,contents⟩ := root proof semantic y1 view accepted
  have bounds := AspisS1AcceptedSliceRange.accepted_range proof part 7751#usize 7783#usize range
  have len : 7783 ≤ proof.val.length := by simpa using bounds.2.1
  have actual := range_total proof 7751#usize 7783#usize (by decide) len
  have same := Result.ok.inj (range.symm.trans actual)
  have physical : bytesOf root.val = OraclePortCompactDraft.slice parsed.wire 7751 32 := by
    rw [contents,same,bytes_sub,wire]
    rfl
  have rootBytes := MultiproofConePhysicalTransport.digest_bytes root
  have decoded : OraclePortCompactDraft.root2 parsed = bytes (decodeState root) := physical.symm.trans rootBytes.symm
  refine ⟨root,field,?_⟩
  simp only [OraclePortBatchDraft.committedRoot,show ¬(2:Nat)=0 by decide,
    show ¬(2:Nat)=1 by decide,if_false,decoded,SemanticRecordCodec.decodeState_bytes,Option.getD_some]

#print axioms root
#print axioms model
end AspisR1.AuS1_RootSource
end
