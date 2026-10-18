#!/usr/bin/env python3
"""Read-only all-row/current-sampler archive audit. No build or runtime run."""
from pathlib import Path
import hashlib,json,re,tarfile
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest();s=json.loads((E/'SUMMARY.json').read_text());a=E/'actual-allrows-sampler-current-proof.tar.gz';assert sha(a.read_bytes())==s['archive_sha256']
with tarfile.open(a)as t:
 files={p.name:t.extractfile(p).read()for p in t if p.isfile()}
expected=[('ExtractedActualAllRows','actual-allrows-a',1),('R1SamplerBlockRank','sampler-rank-a',1),('AspisV8R19.SqueezeOracleBridge','sampler-refresh-0',10),('AspisV8R19.SamplerWordBridge','sampler-refresh-1',5),('R1SamplerByteWord','sampler-refresh-2',1),('R1SamplerBytePass','sampler-refresh-3',2),('R1SourceSamplerByteRank','sampler-refresh-4',7),('ExtractedQM31SamplerCorrect','sampler-correct-b',7),('ExtractedDigest32SamplerTransport','sampler-transport-a',9)]
for target,attempt,count in expected:
 r=json.loads(files['runs/'+attempt+'/receipt.json']);assert r==s['results'][target]and r['exit_status']==0 and r['process_swaps']==0 and r['limits']['memory.swap.max']=='0';raw=files['sources/'+target.replace('.','/')+'.lean'];assert sha(raw)==r['source_sha256'];assert sha(files['runs/'+attempt+'/input-manifest.json'])==r['input_manifest_sha256']
 if target in ['ExtractedActualAllRows','ExtractedDigest32SamplerTransport']:assert raw==(BASE/'lean'/(target+'.lean')).read_bytes()
 log=files['runs/'+attempt+'/lean.log'].decode();reports=re.findall(r"^'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",log,re.M);assert len(reports)==count,(target,len(reports));assert 'sorryAx'not in log and ': error:'not in log and 'error('not in log
 for name,axioms in reports:assert set(q.strip()for q in axioms.split(',')if q.strip())<={'propext','Classical.choice','Quot.sound'},(name,axioms)
audit=json.loads(files['sampler-current-alignment-audit.json']);assert len(audit['conflicts'])==8 and all(q['same_source']for q in audit['conflicts']);assert len(audit['rebuild_targets'])==7
pins=json.loads(files['sampler-current-object-pins.json'])['modules']
for q in audit['conflicts']:assert pins[q['module']]['objects']['.olean']['sha256']==q['current_object_sha256']
for name in audit['custom_dependency_order']+['ExtractedDigest32SamplerTransport']:
 p=pins[name];assert sha(files['sources/'+name.replace('.','/')+'.lean'])==p['source_sha256'],name
failed=json.loads(files['runs/sampler-refresh-5/receipt.json']);assert failed['exit_status']==1 and "RawReducerNat.olean.server"in files['runs/sampler-refresh-5/lean.log'].decode();assert failed['source_sha256']==s['results']['ExtractedQM31SamplerCorrect']['source_sha256']
print(json.dumps({'status':'PASS','focused_targets':9,'standard_or_empty_axiom_reports':43,'identical_source_conflicts_resolved_with_current_objects':8,'sampler_reverse_dependents_refreshed':7,'all_rows_from_actual_first':True,'failed_missing_sidecar_retained':True,'builds_executed':False}))
