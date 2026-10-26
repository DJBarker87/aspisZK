from pathlib import Path
from collections import Counter
import copy,hashlib,json,re
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bp=R/'evidence/recount7-20261026/Rc7_premises.json';base=json.loads(bp.read_text())
log=(E/'FGm_013/stdout.log').read_text()
for name,label in [('Rc7_Top.deployed','RC7_BEFORE'),('FIo_Accepted.deployed','BEFORE'),('FGm_Headline.deployed','AFTER'),('FGm_Nonvacuity.composed','NONVACUITY')]:
 start=log.index('@AspisR1.'+name+' :');end=log.find('\n@AspisR1.',start+1)
 if end<0:end=log.index('\ndef AspisR1.FGm_Owners.Owners',start)
 (E/('FGm_'+label+'.lean.txt')).write_text(log[start:end].rstrip()+'\n')
before=(E/'FGm_BEFORE.lean.txt').read_text();after=(E/'FGm_AFTER.lean.txt').read_text()
assert before.replace('FIo_Accepted.deployed','FGm_Headline.deployed').replace('FGl_PreparedAt.Owners','FGm_Owners.Owners')==after,'Statement differs beyond owner contract'
removed={'F3Y_G_L'+str(i) for i in [133,134,135,136,137,138,147]}
rows=[];diff=[]
for row in base['rows']:
 r=copy.deepcopy(row)
 if r['id'] in removed:
  diff.append(dict(**r,change='removed',proof='FGm_Aligned.values → FGm_Canonical.accepted → FGm_Join/Bound/Cost → FGm_Headline.deployed; SAME installed arithmetic and witness, arbitrary H'))
 else:
  if r['id'].startswith('F3Y_G_'):
   r.update(definition='lean/FGm_Owners.lean#Owners/Holds',evidence='FGm_013 exact kernel statement and expanded contract')
  rows.append(r);diff.append(dict(**r,change='retained'))
def counts(rs):return {k:Counter(r['classification'] for r in rs)[k] for k in ['T','P','G','C']}
def scopes(rs):return {s:counts([r for r in rs if r['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}|{'deduplicated actual plus non-alias deployment':counts([r for r in rs if r['scope']!='deployment alias'])}
# Quarter aliases are duplicated only inside each witness-domain; never across domains.
def distinct(rs):return [r for r in rs if r['id'] not in {'L137','F3Y_G_L137'}]
rawBefore=scopes(base['rows']);rawAfter=scopes(rows);db=scopes(distinct(base['rows']));da=scopes(distinct(rows))
assert rawAfter['actual antecedent']==dict(T=83,P=19,G=13,C=0)
assert da['actual antecedent']==dict(T=83,P=18,G=13,C=0)
assert da['deduplicated actual plus non-alias deployment']==dict(T=89,P=23,G=13,C=0)
result=dict(before='AspisR1.Rc7_Top.deployed specialised as FIo_Accepted.deployed',after='AspisR1.FGm_Headline.deployed',baseline_sha256=sha(bp),method=base['method'],raw_before=rawBefore,raw_after=rawAfter,distinct_before=db,distinct_after=da,distinct_delta=dict(T=0,P=-6,G=0,C=0),removed=sorted(removed),retained_global=[r['id'] for r in rows if r['id'].startswith('F3Y_G_')],added=[],rows=rows,diff=diff,quarter_alias='FIn_QuarterAlias.field_type; two quarter fields are one identical predicate inside each domain. Native L134/L137 untouched; only global quarter is removed.',nonvacuity='FGm_Nonvacuity.composed applies the actual new root at the SAME accepted native cuts and retained snapshots. Conditional; joint release inhabitation not established.',limitations='Five global families remain. No new trust, no global/local identification, no claim of complete Pair value or matching/semantic implementation instance.')
(E/'FGm_premises.json').write_text(json.dumps(result,indent=2)+'\n')
lines=['# Global finish recount','','Rc7 specialised to the already installed FIo dictionary → FGm_Headline.deployed. Only the owner contract changes in the checked statement. No conclusion, game, event, trust item, operational slot or numerical constant changes.','', '|Scope|Before distinct T/P/G/C|After distinct T/P/G/C|','|---|---:|---:|']
for s in db:lines.append('|'+s+'|'+'/'.join(str(db[s][k]) for k in ['T','P','G','C'])+'|'+'/'.join(str(da[s][k]) for k in ['T','P','G','C'])+'|')
lines+=['','Distinct delta −6P. Raw historical delta −7 rows: actual83T/26P/13G→83T/19P/13G; combined89T/31P/13G→89T/24P/13G. Quarter aliases account for the difference. Deployment rows and every native-local finish row are retained. No inherited removal is credited twice.','', '|Global row|Disposition|','|---|---|']
for r in base['rows']:
 if r['id'].startswith('F3Y_G_'):lines.append('|'+r['id']+' / '+r['meaning']+'|'+('REMOVED: source-derived rounds/dot on the same accepted witness, arbitrary H' if r['id'] in removed else 'RETAINED: '+r['meaning'])+'|')
lines+=['','Full exact before/after/non-vacuity statements: FGm_BEFORE.lean.txt,FGm_AFTER.lean.txt,FGm_NONVACUITY.lean.txt. FGm_RC7_BEFORE.lean.txt preserves the unspecialised original. FGm_Owners.weaken proves that the old contract implies the new one on identical guards; no shape/success restriction is added to Owners. Shape is derived in the proof.','', 'Conditional non-vacuity uses the actual new root at the same native cuts and exported successful source/runtime executions, positive zero-query margin. It retains trust,game,native acceptances,snapshots and the five remaining global laws; joint complete release non-vacuity remains open.']
(E/'FGm_LEDGER.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(distinct_before=db,distinct_after=da,removed=sorted(removed)),indent=2))
