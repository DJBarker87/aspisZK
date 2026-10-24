#!/usr/bin/env python3
"""Audit exact named codec port and two-transaction owned consumer specialization."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
target='S6CurrentNamedForestPortV1';attempt='s6-current-named-forest-port-v10';r=load(E/attempt/'receipt.json');p=S/(target+'.lean');s=p.read_text();a=load(E/'accepted-targets.json')['targets'][target];pins=load(E/'s6-current-named-forest-port-import-pins.json')
assert r['exit_status']==0 and r['swaps']==0 and '-j1' in r['command'] and '-M4400' in r['command']
assert a['receipt']==attempt+'/receipt.json'
assert sha(p)==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][target]['source_sha256']
assert r['object_sha256']==pins['targets'][target]['object_sha256']
assert len(r['print_axioms'])==3
for name in ['fullForestAcceptedRoundtrip','reconstructed_bytes','owned_public_field']:
 report=next(x for x in r['print_axioms'] if x.startswith("'AspisS6CurrentNamedForestPort."+name+"'"))
 m=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert m and set(re.findall(r'[A-Za-z_.]+',m[1]))<={'propext','Classical.choice','Quot.sound'}
assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',s,re.M)
assert 'FullForestAcceptedRoundtrip (install ops vops)' in s
consumer=s[s.index('theorem owned_public_field'):]
assert '(fullForestAcceptedRoundtrip :' not in consumer
assert 'ChildInputRetention (install ops vops) c' in consumer and '(validated.statement = statement →' in consumer
assert 'AspisR1.S2Y_ForestPublic.owned_public_field (install ops vops) c' in consumer
reused=E/'s6-current-named-forest-reused';manifest=load(reused/'manifest.json')
for n,row in manifest['targets'].items():
 assert sha(reused/(n+'.lean'))==row['source_sha256']
 assert sha(reused/(n+'-receipt.json'))==row['receipt_sha256']
 rr=load(reused/(n+'-receipt.json'));assert rr['exit_status']==0 and rr['source_hashes'][n+'.lean']==row['source_sha256']
for n,h in load(E/'s6-current-named-forest-port-tool-pins.json')['scripts'].items():assert sha(R/n)==h
for n,h in load(E/'s6-current-named-forest-port-reused-pins.json')['packets'].items():assert sha(E/n)==h
print(json.dumps(dict(target=target,exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=0,standard_axiom_reports=3,named_full_forest_codec_premise_discharged=True,child_input_retention_retained=True,reconstructed_statement_identity_retained=True,whole_s6_closed=False)))
