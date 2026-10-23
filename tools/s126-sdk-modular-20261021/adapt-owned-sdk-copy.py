#!/usr/bin/env python3
"""Reuse literal-equal complete SDK/error types for the emitted copy loop."""
from pathlib import Path
import sys,re,json,hashlib
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021'
I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(parents=True,exist_ok=True)
t=(I/'Types.lean').read_text();f=(I/'Funs.lean').read_text();prior=(D/'S2SdkOwnedTypesV1.lean').read_text()
def declarations(s):
 ms=list(re.finditer(r'^(structure|inductive|def) ([A-Za-z0-9_.]+)',s,re.M));rows={}
 for i,m in enumerate(ms):
  end=ms[i+1].start() if i+1<len(ms) else s.index('\nend ',m.end())
  doc=s.find('\n/--',m.end(),end)
  if doc!=-1:end=doc
  rows[m[2]]=s[m.start():end].strip()
 return rows
new=declarations(t);old=declarations(prior)
old['solana_program_error.ProgramError']=declarations((D/'S2OwnedStage1TypesV1.lean').read_text())['solana_program_error.ProgramError']
norm=lambda s:re.sub(r'\s+',' ',s).strip()
rename=lambda s:s.replace('aspis_s126_owned_sdk.','')
assert len(new)==5,len(new)
pins={}
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
for name,body in new.items():
 mapped=rename(name);assert mapped in old,mapped
 assert norm(rename(body))==norm(old[mapped]),mapped
 pins[name]=dict(reused=mapped,normalized_body_equal=True,emitted_sha256=sha(body),existing_sha256=sha(old[mapped]))
raw=f;f=rename(f).replace('import AspisS2SdkCopyReference.Types','import S2SdkOwnedModelV1')
namespace='AspisS2OwnedStage1.SdkReference.CopyLoop'
f=f.replace('namespace AspisS2SdkCopyReference','namespace '+namespace).replace('end AspisS2SdkCopyReference','end '+namespace)
f=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',f,flags=re.M)
assert 'axiom ' not in f and 'sorry' not in f
f+='\n#print axioms '+namespace+'.copy_step\n#print axioms '+namespace+'.copy_in_place\n'
(O/'S2SdkCopyLoopModelV1.lean').write_text(f)
(O/'sdk-copy-loop-emission-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',types_sha256=sha(t),funs_sha256=sha(raw),source_sha256=sha(f),reused_types=pins,external_callbacks=[],qualification='Exact full owned SDK/error types reused after five literal declaration checks, with external crate name qualification removed. Both emitted byte-step and count loop are retained. Count/totality, original final-assignment equality and native/frozen whole-copy/caller transport are separate gates.'),indent=2)+'\n')
