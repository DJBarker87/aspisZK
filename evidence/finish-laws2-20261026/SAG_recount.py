"""Rc3 atomic quantified-law ledger, at the explicitly installed native scalar instance.
No credit for local dot helpers until the deployed consumer uses that instance.
"""
from pathlib import Path
from collections import Counter
import hashlib,json
P=Path(__file__).resolve().parent
R=P.parents[1]
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
basefile=R/'evidence/recount3-20261026/Rc3_premises.json'
before=json.loads(basefile.read_text())
saf=json.loads((R/'evidence/finish-laws-20261026/SAF_premises.json').read_text())
removed={v['id']:dict(v) for v in saf['assigned_rows'] if v['change']=='removed'}
new_reason='ALL-INPUT native wide mul_m31 semantics plus symbolic quarter identity, at SAG_ScaleConfig.configuration; actual multiplication is total on every raw input.'
for row in before['rows']:
    if row['id'] in {'L134','L137'}:
        removed[row['id']]={**row,'change':'removed','theorem':'AspisR1.SAG_StageScale.quarter',
            'reason':new_reason,'checked_top':'AspisR1.SAG_Deployed.deployed'}
assert len(removed)==21
blockers={v['id']:v['blocker'] for v in saf['assigned_rows'] if v['change']=='open' and v['id'] not in removed}
blockers['L147']='finish.dot remains abstract at SAG_ScaleConfig. SAG_ShapeDot.value proves the sourceDot meaning on the SAME enriched native witness; SAG_NativeFull/SecondFull retain its message ranges. Install sourceDot, propagate that enriched witness through the deployed chain, and derive its 64-weight length from reader/query/flush shape. Decoder agreement and all 64 field/weight reader meanings are now proved, not remaining arithmetic assumptions.'
rows=[]
diff=[]
for row in before['rows']:
    if row['id'] in removed:
        diff.append(removed[row['id']])
    else:
        new={**row,'status':'retained'}
        if row['id'] in blockers:new['blocker']=blockers[row['id']]
        rows.append(new)
        diff.append({**new,'change':'retained'})
assigned=[]
for row in saf['assigned_rows']:
    if row['id'] in removed:assigned.append(removed[row['id']])
    else:assigned.append({**row,'blocker':blockers[row['id']]})
assert len(assigned)==31 and len(blockers)==10

def counts(items):
    return {'rows':len(items),'classes':dict(Counter(v['classification'] for v in items)),
        'owners':dict(Counter(v['owner'] for v in items))}
scopes={s:counts([v for v in rows if v['scope']==s]) for s in ['actual antecedent','deployment only','deployment alias']}
scopes['all retained audit rows']=counts(rows)
scopes['deduplicated actual plus non-alias deployment']=counts([v for v in rows if v['scope']!='deployment alias'])
assert scopes['actual antecedent']['classes']=={'T':82,'P':92}
assert scopes['actual antecedent']['owners']=={'external':85,'lead':18,'session A':71}
assert scopes['deduplicated actual plus non-alias deployment']['classes']=={'T':88,'P':105}
out={'actual_theorem':'AspisR1.SAG_Deployed.deployed','baseline_theorem':before['actual_theorem'],
    'baseline':str(basefile.relative_to(R)),'baseline_sha256':sha(basefile),'method':__doc__,
    'source_scope':'Explicit native quarter/mulM installation. Source associations and all outcomes use that exact dictionary. No equality with every arbitrary seed is asserted.',
    'strict_scope':'SAG_ScaleScope.compatible proves unchanged dictionary when the seed already has those two source slots. These equalities are not new deployed hypotheses.',
    'unrestricted_result':'SAG_SharedDeployed removes only the duplicate quarter row; actual82T+93P, deduplicated88T+106P.',
    'removed_actual_P':21,'new_vs_SAF_P':2,'removed_actual_T':0,'added_law_families':0,
    'counts':scopes,'rows':rows,'diff':diff,'assigned_rows':assigned,
    'quantifier_note':'Same carriers, source cuts, actual operands, model inputs, conditional guards, failure event and numerical conclusion; explicit source dictionary specialization is separately recorded. Generic QuarterMeaning proof inputs are discharged at the top and absent from its result.',
    'nonvacuity':'SAG_ScaleNonvacuity proves all-input source multiplication totality and the actual returned quarter value. Existing Rc3 same-cut conditional non-vacuity retained. No joint inhabitation of every remaining runtime/crypto/model law or old frozen2 raw join is claimed.'}
(P/'SAG_premises.json').write_text(json.dumps(out,indent=2)+'\n')
lines=['# Finish-law row table','','Counted successor: `AspisR1.SAG_Deployed.deployed` at `SAG_ScaleConfig.configuration`. Baseline: `AspisR1.Rc3_Top.deployed`. See SAG_STAGE3.md for the explicit source-instance scope.','','| Row | Law | Status | Theorem or exact blocker |','|---|---|---|---|']
for v in sorted(assigned,key=lambda v:v['id']):
    detail=('`'+v['theorem']+'`: '+v['reason']) if v['change']=='removed' else v['blocker']
    lines.append(f"| {v['id']} | {v['name']} | {v['change']} | {detail.replace('|','/')} |")
lines+=['','Source-specific actual: **82T+113P →82T+92P**; relative SAF **82T+94P →82T+92P**.',
    'Session A92→71; lead18/external3 unchanged. Actual+non-alias deployment **88T+126P →88T+105P**.',
    'Assigned31→10: pairing5, matching1, semantic3, dot1. Nineteen removals are inherited; two are this source-instance discharge.',
    'The unrestricted SAG_SharedDeployed has only the duplicate-row delta1. No blanket source equality or deployed100-bit claim.']
(P/'SAG_ROWS.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(scopes,indent=2))
