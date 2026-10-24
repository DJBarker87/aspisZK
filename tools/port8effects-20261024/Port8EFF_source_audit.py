#!/usr/bin/env python3
"""Exact lexical undo of ONLY effect-lift constructors, then source comparison.
This is source-transformation evidence alongside the kernel source theorem,
not a new compiler/ELF refinement certificate.
"""
from pathlib import Path
import re,json,hashlib,difflib
R=Path(__file__).resolve().parents[2];L=R/'docs/research/100bit-spend-path-20261013/lean';E=R/'evidence/port8effects-20261024'
native=L/'Port4A_NativeReader.lean';lifted=L/'Port8EFF_NativeReader.lean'
source=native.read_text().split('def resume ',1)[1].split('\n#print axioms',1)[0].split(':= do',1)[1]
code=lifted.read_text().split('def program ',1)[1].split('\nprivate theorem',1)[0].split(':= do',1)[1]
reads=re.findall(r'let (\w+) ← read (\w+)',code)
assert reads==[('a','s3'),('a1','s5'),('a2','s9')],reads
steps=0
while 'liftResult (' in code:
 start=code.index('liftResult (');opened=start+len('liftResult ');depth=1;end=opened+1
 while depth:
  if code[end]=='(':depth+=1
  elif code[end]==')':depth-=1
  end+=1
 code=code[:start]+code[opened+1:end-1]+code[end:];steps+=1
code=re.sub(r'\bread (s3|s5|s9)\b',r'aspis_coredigestDigest32Inst.digest hash \1',code)
code=re.sub(r'\bpure\b','ok',code).replace('Port4A_NativeReader.tail','tail')
normalize=lambda s:re.sub(r'\s+','',s)
if normalize(code)!=normalize(source):
 print('\n'.join(difflib.unified_diff(source.splitlines(),code.splitlines())))
 raise AssertionError('Native source/control token mismatch after undoing only effect constructors')
tail=native.read_text().split('def tail ',1)[1].split('\ndef resume',1)[0]
assert not re.search(r'\.digest\b',tail)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out={'schema':'exact-effect-lift-source-audit-v1','native_source':str(native.relative_to(R)),'native_sha256':sha(native),'lifted_source':str(lifted.relative_to(R)),'lifted_sha256':sha(lifted),'ordered_digest_instructions':[{'return':a,'parts':p} for a,p in reads],'pure_lifts':steps,'inverse_transformation':'Remove exactly liftResult outer parentheses; read s3/s5/s9 becomes same native digest instruction; pure becomes ok; native tail qualification removed. All other non-whitespace tokens identical.','tail_direct_digest_free':True,'qualification':'Source/control audit plus Port8EFF_NativeReader.source kernel theorem. Existing extraction/Std/allocator/native helper/ABI interpretations retained; no ELF identity claim.'}
(E/'source-effect-audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'source_control_identical':True,'digest_instructions':len(reads),'pure_lifts':steps}))
