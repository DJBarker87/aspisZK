#!/usr/bin/env python3
"""Audit actual named S6 admission removal from physical byte consumers."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s126-current-caller-20261021';S=B/'lean-candidates/s126-caller-boundary-20261021';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
rows={'S6CurrentPublicAdmissionV1':'s6-current-public-admission-v2','S6CurrentByteSubstitutionV1':'s6-current-byte-substitution-v1'};a=load(E/'accepted-targets.json')['targets'];pins=load(E/'s6-current-public-admission-import-pins.json');wall=0.;peak=0;reports=0
for target,attempt in rows.items():
 r=load(E/attempt/'receipt.json');p=S/(target+'.lean');assert r['exit_status']==0 and r['swaps']==0
 assert sha(p)==sha(E/attempt/'source.lean')==r['source_sha256']==pins['targets'][target]['source_sha256']
 assert a[target]['receipt']==attempt+'/receipt.json' and pins['targets'][target]['object_sha256']==r['object_sha256']
 assert '-j1' in r['command'] and '-M4400' in r['command']
 assert not re.search(r'\b(sorry|native_decide)\b|^\s*(axiom|opaque)\b|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M)
 for report in r['print_axioms']:
  m=re.search(r'depends on axioms:\s*\[([^]]*)\]',report,re.S);assert m and set(re.findall(r'[A-Za-z_.]+',m[1]))<={'propext','Classical.choice','Quot.sound'};reports+=1
 wall+=r['wall_seconds'];peak=max(peak,r['peak_rss_bytes'])
source=(S/'S6CurrentPublicAdmissionV1.lean').read_text();assert 'Port1_ByteDriver.PublicAdmission (install ops vops)' in source and 'AspisS6CurrentCodecInstallation.accepted_inverse pub statement run' in source
consumer=(S/'S6CurrentByteSubstitutionV1.lean').read_text();assert '(admission :' not in consumer and 'Port1_DriverSubstitution.BodyJoins source model' in consumer and 'Port1_Library.TrustedStd ops' in consumer
O=E/'s6-current-public-admission-reused'
for n,row in load(O/'manifest.json')['targets'].items():assert sha(O/(n+'.lean'))==row['source_sha256'] and sha(O/(n+'-receipt.json'))==row['receipt_sha256']
for n,h in load(E/'s6-current-public-admission-tool-pins.json')['scripts'].items():assert sha(R/n)==h
for n,h in load(E/'s6-current-public-admission-reused-pins.json')['packets'].items():assert sha(E/n)==h
assert reports==4
print(json.dumps(dict(targets=2,wall_seconds=wall,peak_rss_bytes=peak,swaps=0,standard_axiom_reports=reports,named_PublicAdmission_discharged=True,physical_byte_transport=True,source_driver_substitution=True,thirteen_body_joins_retained=True,frozen2_model_order=False,native_SDK_binding=False,whole_s6_closed=False)))
