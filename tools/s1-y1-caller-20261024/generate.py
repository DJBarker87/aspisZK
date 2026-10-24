#!/usr/bin/env python3
from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];S=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
def emit(name,text):
 p=S/(name+'.lean')
 if '--check' in sys.argv:assert p.read_text()==text,name
 else:p.write_text(text)
s=(S/'S1PrepareBufferRecombineV1.lean').read_text().replace('import S1NativeCompactEntryLengthV1','import S1PrepareBufferRecombineV1')
s=s.replace('semantic_recombined','y1_recombined').replace('exactly the first','exactly the second')
s=s.replace('core.slice.index.SliceIndexRangeToUsizeSlice','core.slice.index.SliceIndexRangeFromUsizeSlice').replace('{«end»:=cut}','{start:=cut}')
s=s.replace('returned=semantic','returned=y1').replace('alloc.vec.Vec.index_RangeTo_spec','alloc.vec.Vec.index_RangeFrom_spec')
s=s.replace('change returned.val=semantic.val','change returned.val=y1.val').replace('simp [List.slice]','exact List.drop_left')
emit('S1PrepareBufferY1RecombineV1',s)
s=(S/'S1WideViewSemanticV1.lean').read_text().replace('import S1WideViewVariantV1','import S1WideViewSemanticV1').replace('wide_view_semantic','wide_view_y1').replace('sourceView_semantic','sourceView_y1')
s=s.replace('out.semantic=semantic','out.y1=y1').replace('view.semantic=semantic','view.y1=y1').replace('verifier.View.semantic','verifier.View.y1').replace('exact semantic slice','exact Y1 slice')
emit('S1WideViewY1V1',s)
s=(S/'S1PrepareExpansionBuffersV1.lean').read_text().replace('import S1PrepareBufferRecombineV1','import S1PrepareBufferY1RecombineV1').replace('namespace AspisR1CurrentCaller.PrepareBuffers','namespace AspisR1CurrentCaller.PrepareBothBuffers').replace('end AspisR1CurrentCaller.PrepareBuffers','end AspisR1CurrentCaller.PrepareBothBuffers')
a=s.index('    ∃ (off0 off1 : Usize)');b=s.index(' := by',a)
s=s[:a]+'''    ∃ (off0 off1 off2 : Usize)
      (stored initial expanded storedY1 initialY1 expandedY1 semantic y1 : Slice U8)
      (v : verifier.View) (sem : r1_semantic.Verified H),
      compact.OFF_SEMANTIC ops=ok off0 ∧ compact.OFF_Y1 ops=ok off1 ∧
      compact.OFF_INACTIVE ops=ok off2 ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=off0,«end»:=off1}=ok stored ∧
      ops.op10 stored initial=ok (.Ok (),expanded) ∧
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=off1,«end»:=off2}=ok storedY1 ∧
      ops.op11 storedY1 initialY1=ok (.Ok (),expandedY1) ∧
      semantic=expanded ∧ y1=expandedY1 ∧
      ops.op5 proof semantic y1=ok (.Ok v) ∧
      ops.op9 D pub v.semantic hash none=ok (.Ok sem) ∧
      ops.op8 D sem v hash scratchIn=ok (.Ok out,scratchOut)'''+s[b:]
a=s.index('            exact ⟨off0,off1,storedSemantic')
b=s.index('\n\n#print axioms',a)
s=s[:a]+'''            have sameY1 := AspisS1PrepareBufferRecombine.y1_recombined logical deref split i
              semantic1 y11 y1 hderef hsplit
              (semanticLength storedSemantic split.1.1 (.Ok ()) semantic1 hexpSemantic)
              (valueLength storedY1 split.1.2 (.Ok ()) y11 hexpY1) hy1
            exact ⟨off0,off1,off2,storedSemantic,split.1.1,semantic1,storedY1,split.1.2,y11,
              semantic,y1,v,sem,hoff0,hoff1,hoff2,hstoredSemantic,hexpSemantic,hstoredY1,hexpY1,
              sameSemantic,sameY1,hrv,hrs,h⟩'''+s[b:]
s=s.replace('retaining its actual compact input,\nexpansion and reconstructed semantic slice','retaining both actual compact inputs,\nexpansions and reconstructed semantic/Y1 slices')
emit('S1PrepareBothBuffersV1',s)
s=(S/'S1ValuesOwnedPrepareY1V1.lean').read_text().replace('import S1PrepareCodecCallsV1','import S1PrepareBothBuffersV1\nimport S1WideViewY1V1\nimport S1ClaimY1ReadsV1').replace('theorem prepare_y1','theorem prepare_view_y1').replace('#print axioms prepare_y1','#print axioms prepare_view_y1')
a=s.index('    ∃ (stored initial expanded semantic y1');b=s.index('  have add1',a)
s=s[:a]+'''    ∃ (stored initial semantic : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified H),
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
        proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
      expandValues stored initial=ok (.Ok (),view.y1) ∧
      stored.length=464 ∧ initial.length=928 ∧ view.y1.length=928 ∧
      (∀ j, j<928 → view.y1.val[j]?=
        if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8) ∧
      sourceView proof semantic view.y1=ok (.Ok view) ∧
      (NativeBuffers.install (withValues ops) nativeValues R B).op9 D pub view.semantic hash none=ok (.Ok sem) ∧
      (NativeBuffers.install (withValues ops) nativeValues R B).op8 D sem view hash input=ok (.Ok prepared,scratch) ∧
      ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
        AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧
        AspisR1CurrentPreparedClaim.Concrete.Canonical parsed := by
  have semanticLength : ∀ bytes output status updated,
      (NativeBuffers.install (withValues ops) nativeValues R B).op10 bytes output=ok (status,updated) →
        updated.length=output.length := by
    intro bytes output status updated call
    exact AspisS1NativeCompactLengths.semantic_length nativeValues bytes output updated status call
  have valueLength : ∀ bytes output status updated,
      (NativeBuffers.install (withValues ops) nativeValues R B).op11 bytes output=ok (status,updated) →
        updated.length=output.length := by
    intro bytes output status updated call
    exact length_frame bytes output updated status call
  obtain ⟨off0,off1,off2,storedSemantic,initialSemantic,expandedSemantic,stored,initial,expanded,
    semantic,y1,view,sem,hoff0,hoff1,hoff2,hstoredSemantic,hsemantic,hstored,hvalues,
    semanticEq,y1Eq,hview,hsem,hnew⟩ :=
    PrepareBothBuffers.prepare_buffers (NativeBuffers.install (withValues ops) nativeValues R B)
      semanticLength valueLength D pub proof hash prepared input scratch success
  subst semantic
  subst y1
'''+s[b:]
a=s.index('  refine ⟨stored,initial,expanded,semantic,y1,view,sem')
b=s.index('\n\n#print axioms',a)
s=s[:a]+'''  change sourceView proof expandedSemantic expanded=ok (.Ok view) at hview
  have viewY1 := sourceView_y1 proof expandedSemantic expanded view hview
  have fields := original_new_y1_fields D proof expandedSemantic expanded view sem hash prepared input scratch hview hnew
  refine ⟨stored,initial,expandedSemantic,view,sem,hstored,?_,storedSize,initialSize,?_,?_,?_,hsem,hnew,fields⟩
  · rw [viewY1]
    exact hvalues
  · rw [viewY1]
    exact expandedSize
  · intro j bound
    rw [viewY1]
    exact bytes j (by omega)
  · rw [viewY1]
    exact hview
'''+s[b:]
s=s.replace('open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared','open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation')
s=s.replace('all expanded Y1 bytes and downstream View/semantic/Prepared calls','all bytes of the SAME returned View.y1 and downstream semantic/Prepared calls')
emit('S1ValuesOwnedPrepareViewY1V1',s)
s=(S/'S1ValuesOwnedStage1Y1V1.lean').read_text().replace('import S1ValuesOwnedPrepareY1V1','import S1ValuesOwnedPrepareViewY1V1').replace('owned_stage1_y1','owned_stage1_view_y1')
s=s.replace('open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared','open AspisR1CurrentCaller AspisR1CurrentCaller.BorrowedClaimPrepared AspisR1CurrentCaller.InstalledPreparation')
a=s.index('        ∃ stored initial expanded : Slice U8,');b=s.index(' := by',a)
s=s[:a]+'''        ∃ (stored initial semantic : Slice U8) (view : verifier.View) (sem : r1_semantic.Verified Unit),
          core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
            proof {start:=7031#usize,«end»:=7495#usize}=ok stored ∧
          expandValues stored initial=ok (.Ok (),view.y1) ∧
          stored.length=464 ∧ initial.length=928 ∧ view.y1.length=928 ∧
          (∀ j, j<928 → view.y1.val[j]?=
            if j%32<16 then stored.val[(j/32)*16+j%32]? else some 0#u8) ∧
          sourceView proof semantic view.y1=ok (.Ok view) ∧
          (NativeBuffers.install (withValues ops) nativeValues R B).op9
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues R B)
            (FirstComposition.toCurrentPublic
              (AspisR1PublicPreparation.PreparationBinding.preparationPublic statement))
            view.semantic () none=ok (.Ok sem) ∧
          (NativeBuffers.install (withValues ops) nativeValues R B).op8
            (NativeBuffers.callerDigest adapterOps (withValues ops) nativeValues R B)
            sem view () (Array.repeat 29#usize zero)=ok (.Ok prepared,scratch) ∧
          ∀ l : Usize, l.val<29 → ∃ parsed : AspisR1CurrentPreparedClaim.Concrete.E,
            AspisR1CurrentPreparedClaim.ClaimParser.field view.y1 l=ok parsed ∧
            AspisR1CurrentPreparedClaim.Concrete.Canonical parsed'''+s[b:]
s=s.replace('⟨stored,initial,expanded,semantic,y1,view,sem,hstored,hvalues,storedSize,initialSize,\n    expandedSize,formula,hview,hsem,hnew⟩', '⟨stored,initial,semantic,view,sem,hstored,hvalues,storedSize,initialSize,\n    expandedSize,formula,hview,hsem,hnew,fields⟩')
s=s.replace('    prepare_y1 ops R B', '    prepare_view_y1 ops R B')
s=s.replace('    stored,initial,expanded,hstored,hvalues,storedSize,initialSize,expandedSize,formula⟩', '    stored,initial,semantic,view,sem,hstored,hvalues,storedSize,initialSize,expandedSize,formula,hview,hsem,hnew,fields⟩')
s=s.replace('Y1 domain/content and continuation','actual View.y1 bytes, all field reads and continuation')
emit('S1ValuesOwnedStage1ViewY1V1',s)
