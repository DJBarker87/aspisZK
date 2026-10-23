#!/usr/bin/env python3
"""Factor only Lean continuations; verify textual expansion before kernel equality."""
from pathlib import Path
import hashlib,json,re,sys
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
native='--native' in sys.argv
p=(B/'lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean') if native else S/'S6FullSourceCodecV1.lean'
source=p.read_text()
if native:
 from generated_syntax import clean
 source=clean(source)
name=('pool_v1.pair_terminal.' if native else 'aspis_statement.pool_v1.pair_terminal.')+'decode_pool_v1_pair_verified_afterstate_v1';a=source.index('def '+name+' (');b=source.index('\ndef ',a+4);decl=source[a:b];lines=decl.splitlines();body=lines[1:];parts={}
for j in [0,4,8,12,16]:
 start=48+32*j
 ix=[i for i,l in enumerate(lines) if re.search(r'let s\d+ ←.*bytes \{ start := '+str(start)+r'#usize,',l)]
 assert len(ix)==1
 begin=ix[0];indent=len(lines[begin])-len(lines[begin].lstrip())
 end=next(i for i in range(begin+1,len(lines)) if len(lines[i])-len(lines[i].lstrip())==indent-2 and lines[i].lstrip().startswith('| core.ops.control_flow.ControlFlow.Break'))
 parts[j]=dict(begin=begin,end=end,indent=indent)
params=lambda j:['val1']+['val'+str(3+2*i) for i in range(j)]
call=lambda j:'part_'+str(j)+' bytes '+' '.join(params(j))
normalized=lambda x:re.sub(r'\s+','',x)
chunks={}
for j in reversed(list(parts)):
 d=parts[j];fragment=lines[d['begin']:d['end']]
 nextj=j+4
 if nextj in parts:
  q=parts[nextj];lo=q['begin']-d['begin'];hi=q['end']-d['begin'];fragment=fragment[:lo]+[' '*q['indent']+call(nextj)]+fragment[hi:]
 chunks[j]='\n'.join('  '+l[d['indent']:] for l in fragment)
 # Re-expand the one child call; expansion is exactly the original fragment.
 expanded='\n'.join(fragment)
 if nextj in parts:
  q=parts[nextj];expanded=expanded.replace(' '*q['indent']+call(nextj),'\n'.join(lines[q['begin']:q['end']]),1)
 assert normalized(expanded)==normalized('\n'.join(lines[d['begin']:d['end']]))
root=lines[1:parts[0]['begin']]+[' '*parts[0]['indent']+call(0)]+lines[parts[0]['end']:]
expanded='\n'.join(root).replace(' '*parts[0]['indent']+call(0),'\n'.join(lines[parts[0]['begin']:parts[0]['end']]),1)
assert normalized(expanded)==normalized('\n'.join(body))
out='''import S6FullSourceCodecV1
import Mathlib.Tactic.CongrExclamation
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
noncomputable section
namespace AspisS6SourceCodec.AfterstateFactored
open AspisS6FiveUnrolledCodec
open aspis_statement.pool_v1.pair_terminal

'''
result='Result (core.result.Result PoolV1PairVerifiedAfterstateV1 PoolV1PairVerifierTransportErrorV1)'
for j in reversed(list(parts)):
 out+='def part_'+str(j)+' (bytes : Slice U8) ('+' '.join(params(j))+' : Array aspis_core.field.M31 8#usize) : '+result+' := do\n'+chunks[j]+'\n\n'
out+='def decode (bytes : Slice U8) : '+result+' := do\n'+'\n'.join(root)+'\n\n'
out+='''/-- Full Result equality, including failure/divergence and all Rust errors.
Only beta-expanded Lean continuations differ; native carriers/callees are exact. -/
theorem decode_source (bytes : Slice U8) :
    decode bytes=decode_pool_v1_pair_verified_afterstate_v1 bytes := by
  unfold decode decode_pool_v1_pair_verified_afterstate_v1
  unfold part_0 part_4 part_8 part_12 part_16
  run_tac do
    for _ in [:8] do
      let g ← Lean.Elab.Tactic.getMainGoal
      let t ← g.getType
      let names := t.getUsedConstants.filter fun n =>
        let s := n.toString
        s.startsWith "AspisS6SourceCodec." &&
        (s.splitOn ".").any (fun c => c.startsWith "match_")
      if names.isEmpty then break
      let ids := names.map Lean.mkIdent
      Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $[$ids:ident]*))
  dsimp only
  all_goals with_reducible rfl

#print axioms decode_source
end AspisS6SourceCodec.AfterstateFactored
'''
if native:
 out=out.replace('import S6FullSourceCodecV1','import S6NativeAfterstateEncoderReuseV1')
 out=out.replace('AspisS6SourceCodec.AfterstateFactored','AspisS6NativeAfterstateDecoderFactored')
 out=out.replace('open AspisS6FiveUnrolledCodec','open AspisR1TerminalDecoder')
 out=out.replace('open aspis_statement.pool_v1.pair_terminal','open pool_v1.pair_terminal')
 out=out.replace('s.startsWith "AspisS6SourceCodec."','(s.startsWith "AspisR1TerminalDecoder." || s.startsWith "AspisS6NativeAfterstateDecoderFactored.")')
q=S/('S6NativeAfterstateDecoderFactoredV1.lean' if native else 'S6AfterstateDecoderFactoredV1.lean');m=E/('s6-native-afterstate-decoder-factoring-v1.json' if native else 's6-afterstate-decoder-factoring-v1.json');meta=dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),declaration=name,source_fragment_sha256=hashlib.sha256(decl.encode()).hexdigest(),candidate_sha256=hashlib.sha256(out.encode()).hexdigest(),parts={str(k):v for k,v in parts.items()},textual_expansion_equal=True,qualification='Lean-only continuation factoring of the complete concrete decoder reference. Kernel full Result equality must compile; no Rust rewrite, free child operations, simplified carriers, SDK or release closure.')
if native:meta['qualification']='Lean-only continuation factoring of the complete actual AspisR1TerminalDecoder native decoder. All original native carriers and callees are retained. Full Result source equality must compile; no Rust rewrite, free child operations, SDK or release closure.'
if '--check' in sys.argv:assert q.read_text()==out and json.loads(m.read_text())==meta
else:q.write_text(out);m.write_text(json.dumps(meta,indent=2)+'\n')
