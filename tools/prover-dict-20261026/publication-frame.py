"""Factor the exact emitted publication continuation; helper equations stay explicit."""
from pathlib import Path
import sys
r=Path.cwd();p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';s=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean').read_text();a=s.index('def prover.publish_compact\n');b=s.index('\n/--',a);raw=s[a:b];decl=raw.replace('def prover.publish_compact\n','def publicationFrame (ops : ExternalFuns)\n  (semantic : Slice U8 → alloc.vec.Vec U8 → Result ((core.result.Result Unit compact.CodecError) × alloc.vec.Vec U8))\n  (query : alloc.vec.Vec U8 → host_commitment.Commitment → host_commitment.Commitment → Array U32 22#usize → Slice aspis_core.field.wide_exact.WideExact → host_commitment.PrivateSalts → Result (alloc.vec.Vec U8))\n  (nodes : alloc.vec.Vec U8 → host_commitment.Commitment → host_commitment.Commitment → host_tree.BinaryTree → Array U32 22#usize → Result (core.result.Result (alloc.vec.Vec U8) verifier.Error))\n');decl=decl.replace('  := do\n','  :=\n  letI : ExternalFuns := ops\n  do\n',1).replace('host_compact.compact_semantic s2 out2','semantic s2 out2').replace('prover.append_query_openings out9','query out9').replace('prover.append_node_slots out10','nodes out10');out='''import R1Z.PDict_FmtQueryOpenings
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FmtErase
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]
'''+decl+'''
theorem publication_frame (ops : ExternalFuns) :
    @prover.publish_compact _ ops = publicationFrame ops
      (@host_compact.compact_semantic _ ops)
      (@prover.append_query_openings _ ops) (@prover.append_node_slots _ ops) := rfl
#print axioms publication_frame

theorem erase_420 (ops other : ExternalFuns) :
    @prover.publish_compact _ (replace ops other) = @prover.publish_compact _ ops := by
  rw [publication_frame, publication_frame, erase_396 ops other,
    erase_419 ops other, erase_405 ops other]
  unfold publicationFrame
  rfl
#print axioms erase_420
end R1Z.PDict_FmtErase
''';target=p/'PDict_FmtPublicationFrame.lean'
if '--check' in sys.argv:assert target.read_text()==out
else:target.write_text(out)
