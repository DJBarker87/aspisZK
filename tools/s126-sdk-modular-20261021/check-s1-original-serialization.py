#!/usr/bin/env python3
"""Source-only provenance/statement audit. Does not replay unchanged proofs."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
pins=load(E/'s1-original-serialization-import-pins.json');accepted=load(E/'accepted-targets.json')['targets'];reports=0
rows=[('S1OriginalSerializerInstallationV1','s1-original-serializer-install-v2'),('S1OriginalSerializedRankTraceV1','s1-original-serialized-rank-v3'),('S1OriginalPreparedSerializedCallerV1','s1-original-prepared-serialized-caller-v2')]
for name,attempt in rows:
 r=load(E/attempt/'receipt.json');c=load(E/attempt/'command.json');s=(S/(name+'.lean')).read_text()
 assert r['exit_status']==0 and r['swaps']==0 and '-j1' in c['command'] and '-M4400' in c['command']
 assert sha(S/(name+'.lean'))==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][name]['source_sha256']==accepted[name]['source_sha256']
 assert r['object_sha256']==pins['targets'][name]['object_sha256']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',s,re.M)
 for report in r['print_axioms']:
  match=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert match and set(re.findall(r'[A-Za-z_.]+',match[1]))<={'propext','Classical.choice','Quot.sound'};reports+=1
assert reports==8
# Exact warm producer reuse, rather than reattributing a same-name object.
producer=load(B/'evidence/s5-p6-indexed-carrier-bridge-v2-20261021/manifest.json');p=producer['modules'][0]
selected=next(x for x in pins['modules'] if x['name']=='ToBytesP6IndexedCarrierBridgeV1');assert selected['sha256']==p['object_sha256']
assert sha(B/'evidence/s5-p6-indexed-carrier-bridge-v2-20261021'/p['source'])==p['source_sha256']
for mod,row in producer['direct_import_source_map'].items():
 selected=next(x for x in pins['modules'] if x['name']==mod);assert selected['sha256']==row['object_sha256'],mod
 assert sha(R/row['source'])==row['source_sha256'],mod
# Original serializer implementation file unchanged at both recorded freezes.
overlay=load(E/'s1-m31-embedding-source-overlay.json');rel='crates/aspis-core/src/field/wide_exact.rs';assert len(set(overlay['files'][rel].values()))==1
for rev,d in overlay['files'][rel].items():assert hashlib.sha256(subprocess.check_output(['git','-C',str(R),'show',rev+':'+rel])).hexdigest()==d
rank=(S/'S1OriginalSerializedRankTraceV1.lean').read_text();definition=rank[rank.index('def ExactSerializedRankTrace'):rank.index('/-- Same complete')]
assert '(bytes :' not in definition and '28#u8 (Array.to_slice (expectedBytes v.inactive))' in definition
caller=(S/'S1OriginalPreparedSerializedCallerV1.lean').read_text();sig=caller[caller.index('theorem first_serializers_result_eq'):caller.index(' := by')];assert '(h :' not in sig
P=E/'s1-original-claim-recover';manifest=load(P/'manifest.json');assert set(manifest['files'])=={str(p.relative_to(P)) for p in P.rglob('*') if p.is_file()}-{'manifest.json'}
for rel,d in manifest['files'].items():assert sha(P/rel)==d
for name in ['diagnostic','recover','recursive']:
 r=load(P/name/'receipt.json');assert r['exit_status']!=0 and r['swaps']==0 and r['limits']['memory.swap.max']=='0'
for name,code in [('tool-v1',1),('tool-v2',0)]:
 r=load(P/name/'receipt.json');assert r['exit_status']==code and r['process_swaps']==0 and r['swap_bytes']==0
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert 'eval_loop_symbolic_apply_loop' in (P/'recover/stderr.log').read_text()
assert not any(p.suffix in ['.olean','.exe','.o','.out','.llbc','.rlib','.pyc'] for p in P.rglob('*'))
print(json.dumps(dict(accepted_targets=3,standard_axiom_reports=reports,original_serializer_model_total=True,complete_first_result_preserved=True,row28_source_bytes_derived=True,rust_std_correspondence_closed=False,original_nested_claim_closed=False,whole_s1_closed=False,whole_s6_closed=False)))
