#!/usr/bin/env python3
"""Copy only closed layout declarations from the retained actual extraction.
No Lean launch, native mutation, translation repair or axioms are involved.
"""
from pathlib import Path
import re,json,hashlib,sys
root=Path(__file__).resolve().parents[3]
p=root/'docs/research/100bit-spend-path-20261013/evidence/s4-v10-concrete-queryops-builder-v1-20261021/source-evidence/generated-Funs.lean'
s=p.read_text()
defs={}
for m in re.finditer(r'\bdef\s+([A-Za-z0-9_.]+)',s,re.M):
 end=s.find('\n/--',m.end())
 if end<0:end=s.index('\nend ',m.end())
 text=s[m.start():end].strip()
 text=re.sub(r'\n@\[[^\n]*\]\s*$','',text).strip()
 defs[m[1]]=text
names=['compact.FINAL_LEN','compact.HEADER','compact.OFF_SEMANTIC','compact.SEMANTIC_COMPACT_VALUES','verifier.SEMANTIC_BYTES','compact.LOGICAL_SEMANTIC','compact.COMPACT_SEMANTIC','compact.OFF_Y1','compact.COMPACT_Y1','compact.OFF_INACTIVE','compact.OFF_ROUND0','compact.OFF_FOLDED_ROOT','compact.OFF_ROUND1','compact.OFF_FINAL','compact.OFF_OPENINGS','compact.OPENING','compact.QUERIES','compact.OFF_NODES','compact.MAX_NODES','compact.FIXED','compact.MAX_PROOF','compact.PROOF_BYTES','compact.MAGIC','compact.SLOT_NODES']
# Generate in source dependency order; declarations are not evaluated here.
ordered=[];active=set()
def visit(n):
 if n in ordered:return
 assert n not in active,n
 active.add(n)
 for other in names:
  if other!=n and re.search(r'(?<![\w.])'+re.escape(other)+r'(?![\w.])',defs[n]):visit(other)
 active.remove(n);ordered.append(n)
for name in names:visit(name)
out=root/'docs/research/v8-r0-zk-20261009/lean/R1Z/ProverRwDictionaryLayoutSource.lean'
t='''import Aeneas
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error
namespace R1Z.ProverRwDictionaryLayoutSource

-- Literal retained emitted declaration bodies; no external template imported.
'''+ '\n\n'.join(defs[n] for n in ordered)+'\n\nend R1Z.ProverRwDictionaryLayoutSource\n'
if '--check' in sys.argv:assert out.read_text()==t
else:out.write_text(t)
pins=dict(source=str(p.relative_to(root)),source_sha256=hashlib.sha256(s.encode()).hexdigest(),declarations={n:hashlib.sha256(defs[n].encode()).hexdigest() for n in ordered},output_sha256=hashlib.sha256(t.encode()).hexdigest(),changes='Only namespace and imports; declaration bodies unchanged, generator attributes/options excluded',scope='Retained actual source extraction; no compiler/artifact connection or global native dictionary instance supplied')
if '--check' not in sys.argv:(root/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/native-install/layout-source.json').write_text(json.dumps(pins,indent=2)+'\n')
print(json.dumps(dict(declarations=len(ordered),output_sha256=pins['output_sha256'])))
