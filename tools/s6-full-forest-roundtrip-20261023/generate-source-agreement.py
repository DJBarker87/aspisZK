#!/usr/bin/env python3
"""Compose complete codec equality through small symbolic function equalities.
No normalization of the complete enclosing decoder, no resource overrides.
"""
from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021/s6-five-codec-extraction'
f=(S/'S6FullSourceCodecV1.lean').read_text();ms=list(re.finditer(r'(?m)^(?:def|impl_def)\s+([^\s(:]+)',f));blocks={}
for i,m in enumerate(ms):
 end=ms[i+1].start() if i+1<len(ms) else f.index('\nend AspisS6SourceCodec',m.end())
 blocks[m[1]]=f[m.end():end]
needed=set(json.loads((E/'materialization.json').read_text())['parameterized_definitions'])
deps={n:[q for q in blocks if q!=n and re.search(r'(?<![\w.])'+re.escape(q)+r'(?![\w.])',body)] for n,body in blocks.items()}
order=[];active=set();seen=set()
def visit(n):
 if n in seen:return
 assert n not in active,('cycle',n)
 active.add(n)
 for q in deps[n]:visit(q)
 active.remove(n);seen.add(n);order.append(n)
for n in blocks:visit(n)
ids={n:i for i,n in enumerate(order)};chunk=20
for start in range(0,len(order),chunk):
 ix=start//chunk;name=f'S6SourceAgreementPart{ix:02d}V1';prev=f'S6SourceAgreementPart{ix-1:02d}V1' if ix else 'S6FiveCodecStdOptionsV1'
 hasctx=any(blocks[n].count('←')>70 for n in order[start:start+chunk])
 out=f'import S6FullSourceCodecV1\nimport {prev}\n'+('import S6SourceAgreementContextV1\n' if hasctx else '')+'set_option autoImplicit false\nopen Aeneas Aeneas.Std Result\nnamespace AspisS6SourceCodec.Links\n'+('open AspisS6FiveUnrolledCodec\n' if hasctx else '')
 for n in order[start:start+chunk]:
  i=ids[n];rhs='@AspisS6FiveUnrolledCodec.'+n+(' (AspisS6FiveUnrolledCodec.StdOptions.ops unused)' if n in needed else '')
  if blocks[n].count('←')>70:
   signature,body=blocks[n].split(':=',1)
   params=' '.join(f'(dep_{ids[q]} : codec_type% @AspisS6SourceCodec.{q})' for q in deps[n])
   for q in sorted(deps[n],key=len,reverse=True):body=re.sub(r'(?<![\w.])'+re.escape(q)+r'(?![\w.])','dep_'+str(ids[q]),body)
   out+=f'\nprivate def context_{i} {params}'+signature+':='+body+'\n'
   left=' '.join('(@AspisS6SourceCodec.'+q+')' for q in deps[n])
   right=' '.join('(@AspisS6FiveUnrolledCodec.'+q+(' (AspisS6FiveUnrolledCodec.StdOptions.ops unused)' if q in needed else '')+')' for q in deps[n])
   rewrites=', '.join(f'link_{ids[q]} unused' for q in deps[n])
   out+=f'\ntheorem link_{i} (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :\n    @AspisS6SourceCodec.{n} = {rhs} := by\n  have h : @context_{i} {left} = @context_{i} {right} := by\n    rw [{rewrites}]\n  exact h\n'
  else:
   out+=f'\ntheorem link_{i} (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :\n    @AspisS6SourceCodec.{n} = {rhs} := by\n  unfold AspisS6SourceCodec.{n} AspisS6FiveUnrolledCodec.{n}\n'
   ds=', '.join(f'link_{ids[q]} unused' for q in deps[n])
   out+='  try simp only [AspisS6FiveUnrolledCodec.StdOptions.ops'+(', '+ds if ds else '')+']\n'
   out+='  all_goals rfl\n'
  out+=f'\n#print axioms link_{i}\n'
 (S/(name+'.lean')).write_text(out+'\nend AspisS6SourceCodec.Links\n')
last=(len(order)-1)//chunk
out=f'import S6SourceAgreementPart{last:02d}V1\nset_option autoImplicit false\nopen Aeneas Aeneas.Std Result\nnamespace AspisS6SourceCodec.Agreement\n'
for n in ['encode','decode']:
 i=ids[n];out+=f'\ntheorem {n}_eq (unused : AspisS6FiveUnrolledCodec.StdOptions.SliceArrayEq) :\n    AspisS6SourceCodec.{n} = AspisS6FiveUnrolledCodec.StdOptions.{n} unused := by\n  exact Links.link_{i} unused\n\n#print axioms {n}_eq\n'
(S/'S6FullSourceCodecAgreementV2.lean').write_text(out+'\nend AspisS6SourceCodec.Agreement\n')
(E/'agreement-generation.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',order=order,dependencies=deps,parameterized_old_definitions=sorted(needed),chunks=last+1,qualification=__doc__),indent=2)+'\n')
print(json.dumps(dict(definitions=len(order),chunks=last+1,first='S6SourceAgreementPart00V1')))
