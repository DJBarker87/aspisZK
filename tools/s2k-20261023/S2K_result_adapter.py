"""Reuse exact existing declarations; retain only new extracted result source.
No opaque declaration is installed: encoder names resolve to existing definitions.
"""
from pathlib import Path
import re,json,hashlib,difflib,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2k-20261023'
G=E/f'extract-{int(sys.argv[1]):03d}-generated/S2K_ResultValidationSource';old=D/'lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder'
def split(t):
 chunks=re.split(r'(?=/\*\*|/--)',t);out={}
 for b in chunks:
  code=re.sub(r'/\-[\s\S]*?\-/','',b)
  names=re.findall(r'\b(?:def|impl_def|structure|inductive|abbrev)\s+([^\s:(]+)',code)
  if not names:continue
  out[names[0]]=b
 return out
def canon(b):
 b=re.sub(r'/\-[\s\S]*?\-/','',b)
 b=re.sub(r'@\[[\s\S]*?\]','',b)
 b=b.replace('impl_def ','def ')
 b=re.sub(r'\nend [^\n]*','',b)
 return re.sub(r'\s+','',b)
kept=[];reused=[];mismatches=[]
for part in ['Types','Funs']:
 raw=(G/(part+'.lean')).read_text().replace('S2K_ResultValidationSource','AspisR1TerminalDecoder')
 ref=split((old/(part+'.lean')).read_text())
 for name,b in split(raw).items():
  if name in ref:
   same=canon(b)==canon(ref[name]);reused.append(dict(name=name,exact_modulo_comments_attributes_whitespace=same))
   if not same:mismatches.append((name,b,ref[name]))
  else:kept.append((name,b))
if mismatches:
 for name,a,b in mismatches:
  print('MISMATCH',name);print(''.join(difflib.unified_diff(b.splitlines(True),a.splitlines(True)))[:4000])
 raise SystemExit(1)
text='import S2K_ResultEvent\n\n/-! Actual extracted result validator; only names/duplicate dependencies adapted.\nOpaque encoder declarations are replaced by the already-proved exact definitions\non identical carriers. No new opaque constant or successful-child premise. -/\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option autoImplicit false\nnamespace AspisR1TerminalDecoder\n'
for name,b in kept:text+='\n'+re.sub(r'\nend [^\n]*','',b).rstrip()+'\n'
text+='\n#print axioms pool_v1.pair_forest_terminal.validate_result\nend AspisR1TerminalDecoder\n'
p=D/'lean/S2K_ResultNativeSource.lean';assert not p.exists();p.write_text(text)
(E/'c3-result-adapter.json').write_text(json.dumps(dict(reused=reused,kept=[name for name,b in kept],new_module_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),raw={str(f.relative_to(E)):hashlib.sha256(f.read_bytes()).hexdigest() for f in G.glob('*.lean')},replacements='namespace, imports, duplicate declarations; every reused body equal modulo comments/attributes/whitespace; external signatures resolved to existing definitions'),indent=2)+'\n')
print([n for n,b in kept])
