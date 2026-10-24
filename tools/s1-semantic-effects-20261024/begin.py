#!/usr/bin/env python3
"""Fission exact source continuations; never change guards, order or carriers."""
from pathlib import Path
import re,sys,json,hashlib
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021'
p=B/'lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/AspisR1PublicPreparation/Funs.lean';raw=p.read_text();a=raw.index('def r1_wire.begin\n');b=raw.index('\n/--',a);original=raw[a:b].rstrip();signature,body=original.split(':= do',1)
parts={};working=body
# Extract from the innermost source subtree first, retaining every rejection suffix.
for row in [13,9,5]:
 lines=working.splitlines();pattern=re.compile(r'^\s*let r'+str(row*2)+r' ←')
 start=next(i for i,l in enumerate(lines) if pattern.match(l));indent=len(lines[start])-len(lines[start].lstrip());end=start+1
 while end<len(lines) and (not lines[end].strip() or len(lines[end])-len(lines[end].lstrip())>=indent):end+=1
 segment='\n'.join(l[indent:] for l in lines[start:end])
 parts[row]=segment
 args=f'aspis_coreDigest32Inst prefix1 transcript{row} val val1 val2 val{row-1} index_mut_back{row-4}'
 lines[start:end]=[' '*indent+f'begin{row} '+args]
 working='\n'.join(lines)+'\n'
parts[0]=working.strip('\n')
header='''import S1SemanticCodeSemanticValidatedV1
set_option autoImplicit false
namespace AspisR1PublicPreparation.S1SemanticCode
open Aeneas Aeneas.Std Result
open PreparedHashCode (Code)

'''
result=header
for native in [True,False]:
 for row in [13,9,5,0]:
  name='begin'+(str(row) if row else '')+('_native' if native else '')
  if row:
   sig=f'''def {name} {{H : Type}} (aspis_coreDigest32Inst : aspis_core.Digest32 H)
  (prefix1 : r1_wire.Prefix) (transcript{row} : r1_wire.SemanticTranscript H)
  (val val1 val2 val{row-1} : aspis_core.field.QM31)
  (index_mut_back{row-4} : aspis_core.field.QM31 → Array aspis_core.field.QM31 10#usize) :
  '''+('Result' if native else 'Code')+''' ((core.result.Result r1_wire.Challenges r1_wire.Error) × r1_wire.SemanticTranscript H)
  '''
  else:
   sig=signature.replace('def r1_wire.begin','def '+name)
   if not native:sig=sig.replace('Result ', 'Code ',1)
  code=parts[row]
  for child in [13,9,5]:
   if native:code=code.replace('begin'+str(child)+' ','begin'+str(child)+'_native ')
  if not native:
   code=re.sub(r'\bok\b','pure',code).replace('r1_wire.SemanticTranscript.semantic_validated','semanticValidated')
  # Dedent only extracted continuations; the root already carries its source indentation.
  if row:code='\n'.join('  '+l for l in code.splitlines())
  result+=sig+':= do\n'+code+'\n\n'
result+='\n'.join('#print axioms begin'+(str(n) if n else '') for n in [13,9,5,0])+'\nend AspisR1PublicPreparation.S1SemanticCode\n'
p=S/'S1SemanticCodeBeginV1.lean'
if '--check' in sys.argv:assert p.read_text()==result
else:p.write_text(result)
meta={'schema':'focused-extractor-proof-packet-v1','original_sha256':hashlib.sha256(original.encode()).hexdigest(),'generated_sha256':hashlib.sha256(result.encode()).hexdigest(),'source_subtree_rows':[13,9,5],'captures':'Exact existing transcript, lambda/chi/theta values, previous zc value and mutable-array setter closure; no projected fields','qualification':'Pure and effectful fissions; native-to-original equality and per-helper erasures must be compiled. No production adoption.'};p=E/'s1-semantic-begin-fission-pins.json'
if '--check' in sys.argv:assert json.loads(p.read_text())==meta
else:p.write_text(json.dumps(meta,indent=2)+'\n')
