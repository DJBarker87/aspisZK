#!/usr/bin/env python3
"""Read-only full-statement/pin/axiom audit; no compiler, no source premise installed."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021';P=E/'first-only-20261025'
j=json.loads((P/'manifest.json').read_text())
for rel,h in j['files'].items():assert hashlib.sha256((R/rel).read_bytes()).hexdigest()==h
reports=[]
for row in json.loads((P/'statement-comparison.json').read_text()):
 old=(S/(row['old']+'.lean')).read_text();new=(S/(row['new']+'.lean')).read_text()
 def conclusion(s):return s[s.index('    post = writeBracket'):s.index(' := by',s.index('    post = writeBracket'))]
 assert conclusion(old)==conclusion(new)
 sig=new[new.index('theorem original_sdk_'):new.index('    post = writeBracket')]
 assert all(x not in sig for x in ['native2','hashv','AeneasExtraction'])and 'Stage1Extraction'in sig
 r=json.loads((E/row['attempt']/'receipt.json').read_text());assert r['exit_status']==0 and r['swaps']==0
 assert r['source_sha256']==hashlib.sha256(new.encode()).hexdigest()
 assert (E/row['attempt']/'source.lean').read_text()==new
 assert '-j1'in r['command']and '-M4400'in r['command']
 for audit in r['print_axioms']:
  names=set(re.search(r'\[(.*?)\]',audit,re.S).group(1).replace('\n','').replace(' ','').split(','))
  assert names<={'propext','Classical.choice','Quot.sound'}
 reports.append(dict(target=row['new'],exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=0,axiom_reports=len(r['print_axioms'])))
s=(S/'S6SdkFirstOnlyV1.lean').read_text();definition=s[s.index('def Stage1Extraction'):s.index('theorem stage1_of_full')]
assert 'stage2'not in definition and 'digest'not in definition and 'native1 program accounts data ='in definition and 'stage1_owned ops program accounts data'in definition
assert 'original_sdk_all_cuts'not in s and 'extraction.stage1'not in s[s.index('theorem original_sdk_reached_first'):]
for bad in ['sorry','native_decide','bv_decide','set_option maxRecDepth','set_option maxHeartbeats','axiom ']:assert bad not in s
print(json.dumps(dict(status='PASS',pins=len(j['files']),targets=reports,all_old_conclusions_literal_equal=True,unproved_concrete_stage1_source_binding_retained=True,concrete_digest_oracle_binding_not_disproved_or_discharged_elsewhere=True,whole_S1_S6_closed=False)))
