from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2]; E=R/'evidence/ports3-20261023'; L=R/'docs/research/100bit-spend-path-20261013/lean'
s=(E/'current-children/Funs.lean').read_text(); a=s.index('def verifier.resume\n'); b=s.index('\n/-- ',a)
body=s[a:b]
body=body.replace('def verifier.resume\n','def resume (ops : ResumeOps)\n')
replacements={
 'verifier.checkpoint_size':'ops.checkpointSize',
 'transport.Variant.tag':'ops.tag',
 'transport.Variant.final_len':'ops.finalLen',
 'Slice.Insts.CoreCmpPartialEqArray.ne':'ops.ne',
 'Slice.Insts.CoreCmpPartialEqArray\n        8#usize':'slicePartialEq ops\n        8#usize',
 'verifier.Reader.raw':'ops.raw','verifier.Reader.e':'ops.readE','verifier.Reader.k':'ops.readK',
 'verifier.validate_checkpoint_queries':'ops.validate',
 'verifier.read_checkpoint_semantic_alpha':'ops.readSemanticAlpha',
 'verifier.read_checkpoint_weights':'ops.readWeights',
 'aspis_core.field.QM31.ZERO':'ops.zeroK'}
for old,new in replacements.items():
 assert old in body,old
 body=body.replace(old,new)
body,n=re.subn(r'core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any\s*\(verifier.resume.closure.Insts.CoreOpsFunctionFnMutTupleSharedU8Bool\s*aspis_coredigestDigest32Inst\) i6 \(\)', 'ops.headerAny i6',body); assert n==1
body,n=re.subn(r'let r51 ←\s*aspis_core.r0.heap.filled\s*aspis_core.field.QM31.Insts.CoreMarkerCopy\s*i30 q\s*let r52 ←\s*core.result.Result.map_err\s*\(verifier.resume.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError\s*aspis_coredigestDigest32Inst\)\s*r51 \(\)', 'let r52 ← ops.filled i30 q',body); assert n==1
cut=body.index('                  let b4 ←')
tail=body[cut:]
tail='\n'.join(line[18:] if line.startswith(' '*18) else line for line in tail.splitlines())
body=body[:cut]+'                  tail ops bytes v i4 end1 s6 a2\n'
tail='def tail (ops : ResumeOps) (bytes : Slice U8) (v : transport.Variant)\n    (i4 : U8) (end1 : Usize) (s6 : Slice U8) (a2 : Array U8 32#usize) :\n    Result (core.result.Result (verifier.Prepared × verifier.Accumulator) verifier.Error) := do\n'+ '\n'.join('  '+line for line in tail.splitlines())+'\n'
module='''import Port3_CheckpointInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4A_NativeReader
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1Stage2
/-! Current emitted parent with explicit helper leaves. `filled` includes
allocation's emitted Allocation error map; no allocation success is assumed.
Native helper/std implementations remain independent adoption obligations. -/
'''+tail+body+'''
#print axioms tail
#print axioms resume
end AspisR1.Port4A_NativeReader
end
'''
(L/'Port4A_NativeReader.lean').write_text(module)
def sha(s):return hashlib.sha256(s.encode()).hexdigest()
(R/'evidence/port4a-20261023/reader-emission.json').write_text(json.dumps(dict(input='evidence/ports3-20261023/current-children/Funs.lean',input_sha256=sha(s),start=a,end=b,span_sha256=sha(s[a:b]),module_sha256=sha(module),replacements=replacements,combined_leaves=['headerAny: actual iterator any with emitted b!=0 closure','filled: allocator plus actual map_err Allocation']),indent=2)+'\n')
