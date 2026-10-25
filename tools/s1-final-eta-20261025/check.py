#!/usr/bin/env python3
"""Read-only exact-statement and accepted-axioms audit; no Lean replay."""
from pathlib import Path
import hashlib,json,re
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';S=B/'lean-candidates/s126-caller-boundary-20261021';E=B/'evidence/s126-current-caller-20261021';P=E/'final-eta-20261025'
j=json.loads((P/'manifest.json').read_text())
for p,h in j['files'].items():assert hashlib.sha256((R/p).read_bytes()).hexdigest()==h
old=(S/'S1SdkFirstOnlyPhysicalV1.lean').read_text();new=(S/'S1SdkFirstOnlyEtaV1.lean').read_text();c=json.loads((P/'comparison.json').read_text())
def binders(s):return s[s.index(' {W A M Cv : Type}'):s.index('    post = writeBracket')]
def conclusion(s):return s[s.index('    post = writeBracket'):s.index(' := by',s.index('    post = writeBracket'))]
assert binders(old)==binders(new)
assert conclusion(new).replace(c['added_conjunct']+'\n','')==conclusion(old)
a=(S/'S1ReachedFinalNumericV1.lean').read_text();b=(S/'S1ReachedFinalEtaNumericV1.lean').read_text()
a=a[a.index('def ReachedFinalNumeric'):a.index('\n/-- ACCEPTED-ONLY')]
b=b[b.index('def ReachedFinalEtaNumeric'):b.index('\n\ntheorem of_reached')]
assert b==a.replace('def ReachedFinalNumeric','def ReachedFinalEtaNumeric').replace('(Canonical sem.challenges.eta → Canonical terminalValue →','Canonical sem.challenges.eta ∧ (Canonical terminalValue →')
rows=[]
for target,attempt in [('S1ReachedFinalEtaNumericV1','s1-reached-final-eta-v1'),('S1SdkFirstOnlyEtaV1','s1-sdk-first-only-eta-v1')]:
 r=json.loads((E/attempt/'receipt.json').read_text());src=(S/(target+'.lean')).read_bytes()
 assert r['exit_status']==0 and r['swaps']==0 and r['source_sha256']==hashlib.sha256(src).hexdigest()
 assert (E/attempt/'source.lean').read_bytes()==src and '-j1'in r['command']and '-M4400'in r['command']
 for audit in r['print_axioms']:
  names=set(re.search(r'\[(.*?)\]',audit,re.S).group(1).replace('\n','').replace(' ','').split(','));assert names<={'propext','Classical.choice','Quot.sound'}
 rows.append(dict(target=target,exit_status=0,wall_seconds=r['wall_seconds'],peak_rss_bytes=r['peak_rss_bytes'],swaps=0))
print(json.dumps(dict(status='PASS',pins=len(j['files']),targets=rows,same_binders=True,all_old_conclusions_retained=True,eta_range_from_same_reached_semantic_record=True,terminal_range_still_required=True,actual_source_S1_S6_and_TOTAL_not_closed=True)))
