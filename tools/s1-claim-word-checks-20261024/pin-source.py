#!/usr/bin/env python3
"""Retain exact source identities; never treat verifier.rs as candidate.rs."""
from pathlib import Path
import hashlib,json,subprocess,re
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
revisions=['b2727acd3abf79315d18b754a260f58f4b1c6326','25866ec331cc7ce27dd9956609c11d32fa8fa58a','b797d6d360b460b527c046e37dad1106e8beeabc']
files=['crates/aspis-r1-cost-probe/src/'+x+'.rs' for x in ['verifier','candidate','weights','fast_pairing','r1_semantic','r1_wire','compact']]
rows={};texts={}
for f in files:
 values={r:subprocess.check_output(['git','show',r+':'+f],cwd=R) for r in revisions}
 texts[f]=values
 hashes={r:hashlib.sha256(v).hexdigest() for r,v in values.items()};rows[f]=dict(sha256=hashes,all_equal=len(set(hashes.values()))==1)
 if f.endswith(('/verifier.rs','/candidate.rs')):assert rows[f]['all_equal'],(f,hashes)
 if not f.endswith(('/weights.rs','/fast_pairing.rs')):assert hashes[revisions[1]]==hashes[revisions[2]],(f,hashes)
def function(text,name):
 text=text.decode();start=re.search(r'\bfn\s+'+re.escape(name)+r'\b',text).start();i=text.index('{',start);depth=0
 for j in range(i,len(text)):
  depth+=(text[j]=='{')-(text[j]=='}')
  if depth==0:return text[start:j+1].encode()
 raise AssertionError(name)
spans={}
for file,names in [('weights',['field','powers']),('fast_pairing',['new','push','finish'])]:
 key='crates/aspis-r1-cost-probe/src/'+file+'.rs'
 for name in names:
  values=texts[key]
  if file=='fast_pairing':values={r:v[v.index(b'pub struct EbyKDot'): ] for r,v in values.items()}
  hashes={r:hashlib.sha256(function(v,name)).hexdigest() for r,v in values.items()}
  spans[file+'::'+name]=dict(sha256=hashes,all_equal=len(set(hashes.values()))==1)
  assert hashes[revisions[1]]==hashes[revisions[2]],(file,name)
(E/'s1-native-word-control-source-pins.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',files=rows,relevant_leaf_spans=spans,qualification='Entire native verifier, adopted candidate entry/helper and relevant source files checked separately across frozen/reference/current research revisions. Numeric leaf files weights.rs and fast_pairing.rs differ and are NOT certified equivalent; the older r1_wire.rs also differs from the frozen/current file. Relevant outer leaf spans are pinned separately; matching outer spans do not certify changed transitive numeric helpers. The controller proof has shared normal-return leaf contracts; source/purity/arithmetic/abort leaf interpretation remains explicit. No ELF, SDK or code-lowering equivalence is inferred.'),indent=2)+'\n')
print(json.dumps(dict(files=len(rows),equal_controller_files=all(rows['crates/aspis-r1-cost-probe/src/'+n+'.rs']['all_equal'] for n in ['verifier','candidate']),changed_files=[k for k,v in rows.items() if not v['all_equal']])))
