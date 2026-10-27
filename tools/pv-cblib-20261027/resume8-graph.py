from pathlib import Path
b=Path(__file__).resolve().parents[2]/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s='import R1Z.PV_CBL_BlockStage00\nimport R1Z.PV_CBL_BlockValueFactored\nimport R1Z.PV_CBL_FallbackConstantSource\nimport R1Z.PV_CBL_FallbackArray16\n'
for i in range(16):s+=f'import R1Z.PV_CBL_BlockConstantRead{i:02}\n'
s+='''open Aeneas Aeneas.Std Result
namespace R1Z.PV_CBL_BlockGraph
open PV_CBL_FallbackArray4 PV_CBL_FallbackScalar
set_option autoImplicit false
'''
for i in range(4):
 s+=f'def group{i} (input : Array U32 16#usize) : A4 := pack '+ ' '.join(f'input.val[{x}]!' for x in reversed(range(i*4,i*4+4)))+'\n'
groups=' '.join(f'(group{i} input)' for i in range(4))
s+=f'''def value (state : State) (input : Array U32 16#usize) : State :=
  PV_CBL_BlockStage00.value state state {groups}
def graph (state : State) (input : Array U32 16#usize) : Result (Array U32 8#usize) :=
  PV_CBL_BlockStage00.source (PV_CBL_FallbackStateCodec.encode state)
    (pack state.a state.b state.e state.f) (pack state.c state.d state.g state.h) {groups}
theorem graph_value (state : State) (input : Array U32 16#usize) :
    graph state input = ok (PV_CBL_FallbackStateCodec.encode (value state input)) :=
  PV_CBL_BlockStage00.shape state state _ _ _ _
theorem source (state : State) (input : Array U32 16#usize) :
    PV_CBL_FallbackBlock.sha_fallback_reference.extracted_block
      (PV_CBL_FallbackStateCodec.encode state) input = graph state input := by
  rw [PV_CBL_BlockValueFactored.source]
'''
# Specialize bounds; no large numeral or recurrence is unfolded.
for i in range(8):s+=f'  have hs{i} := PV_CBL_FallbackArrayRead.read (PV_CBL_FallbackStateCodec.encode state) {i}#usize (by decide)\n'
for i in range(16):s+=f'  have hb{i} := PV_CBL_FallbackArrayRead.read input {i}#usize (by decide)\n'
lemmas=['PV_CBL_BlockValueFactored.block','graph','PV_CBL_FallbackConstantSource.source']+[f'PV_CBL_BlockConstantRead{i:02}.source' for i in range(16)]+[f'hs{i}' for i in range(8)]+[f'hb{i}' for i in range(16)]+['bind_tc_ok']
s+='  simp only ['+',\n    '.join(lemmas)+']\n'
for i in range(16):
 s+=f'  conv_rhs => unfold PV_CBL_BlockStage{i:02}.source\n'
 if i>=4:s+=f'  apply PV_CBL_BlockBindExt.bind_ext\n  intro word{i}\n'
 s+=f'  apply PV_CBL_BlockBindExt.bind_ext\n  intro pair{i}\n  rcases pair{i} with ⟨abef{i},cdgh{i}⟩\n'
s+='  conv_rhs => unfold PV_CBL_BlockStage16.source PV_CBL_FallbackFeedForward.source\n  conv_rhs => rw [hs0]; simp only [bind_tc_ok]\n#print axioms value\n#print axioms graph\n#print axioms graph_value\n#print axioms source\nend R1Z.PV_CBL_BlockGraph\n'
(b/'PV_CBL_BlockGraph.lean').write_text(s)
