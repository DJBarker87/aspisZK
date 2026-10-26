#!/usr/bin/env python3
"""Reviewed atomic-family correspondence, mechanically enumerated.

This checks receipts and expanded inventories. It is not a logical-discharge
solver. Different guards and witness domains are never silently identified.
"""
from pathlib import Path
from collections import Counter
import copy, hashlib, json, re
E=Path(__file__).resolve().parent
ROOT=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
basepath=ROOT/'evidence/recount5-20261026/Rc5_premises.json'
base=json.loads(basepath.read_text())
oldpath=ROOT/'evidence/frozen3-head5-20261026/F3X_premises.json'
old=json.loads(oldpath.read_text())
plan=json.loads((E/'F3Y_audit-plan.json').read_text())
logs={};catalog={};evidence=[]
for a in plan:
    d=E/a['attempt'];receipt=json.loads((d/'receipt.json').read_text())
    assert receipt['exit_status']==0,a
    assert sha(ROOT/'lean'/(a['module']+'.lean'))==a['source_sha256'],a
    log=(d/'stdout.log').read_text()
    assert not re.search(r'\berror(?:\(|:)',log),a
    logs[a['module'].removeprefix('F3Y_Audit')]=log
    evidence.append(dict(**a,stdout_sha256=sha(d/'stdout.log')))
    for block in re.split(r'(?=^structure )',log,flags=re.M):
        if not block.startswith('structure ') or 'fields:\n' not in block:continue
        key=re.match(r'structure (\S+)',block)[1]
        fields=block.split('fields:\n',1)[1].split('constructor:',1)[0]
        catalog[key]=dict(fields=fields,field_names=re.findall(r'^  ([\w.α-ωΑ-Ω]+) :',fields,re.M))
oldcat=json.loads((ROOT/'evidence/recount5-20261026/Rc5_field_catalog.json').read_text())
unchanged=[]
for key in oldcat.keys()&catalog.keys():
    assert catalog[key]['fields']==oldcat[key]['fields'],('changed inherited fields',key)
    unchanged.append(key)
assert len(unchanged)>=15,len(unchanged)
root=logs['Composition'].split('@AspisR1.F3Y_Headline.deployed :',1)[1].split('@AspisR1.F3Y_Nonvacuity.composed :',1)[0]
assert 'F3Y_PreparedAt.Owners' in root
assert 'F3T_Runtime.StoredCarrierBinding' in root
assert 'F3T_CanonicalJoin.AcceptedVerifierJoin' not in root
for marker in ['prefixBound','choiceBound','prepareOwner','primitiveOwner','canonicalOwner','domainOwner']:
    assert marker not in root,marker
for marker in ['Rc5_Result.Outcome','CPH_Protection.Facts','CPH_Trace.Facts','CPH_Recorder.Facts',
               'CPH_Game.DeployedPairExecution','CPR_DataPersistence.TwoTransactionLaw',
               'F3Y_SourceClaims.Claims','F3Y_AccountMass.Claims','F3X_ModelClaims.Claims']:
    assert marker in root,marker
assert len(catalog['AspisR1.F3Y_FinishLeaves.PairingRemaining']['field_names'])==3
assert len(catalog['AspisR1.Port4D_Pairing.RoundLaws']['field_names'])==3
assert 'F3Y_FinishLeaves.Holds' in logs['NewOwners']
assert 'F3Y_PreparedAt.At' in logs['NewOwners']
assert 'F3Y_FinishLeaves.PairingRemaining' in logs['NewFinish']
assert 'canonical' not in ' '.join(catalog['AspisR1.F3Y_FinishLeaves.PairingRemaining']['field_names'])
# Preserve exact same Rc5 native/history statement: only the security block
# and explicit global finish premises changed in the new top.
src=(ROOT/'lean/F3Y_Headline.lean').read_text()
assert 'Rc5_Source.source' in src and 'Rc5_Close.from_saf' in src
assert 'CPH_Protection.derive' in src and 'CPH_Recorder.physical' in src
assert 'F3Y_Bound.bound' in src and 'F3Y_Cost.source_cost' in src
remove={'L157','N117','N118','L182'}
removed_reasons={
'L157':'F3Y_Join derives accepted source/model equality OR the SAME single Q+2965 charged account event; F3Y_Bound consumes it at the exact Rc5 dictionary.',
'N117':'The old independent native-account adversary is replaced by the account constructed from the SAME byte prover. Its Q+1921 first-read budget follows from L154. No bound on arbitrary old adversaries is claimed.',
'N118':'The old independent chooseSecond program is absent with that experiment. The constructed byte-prover account includes the rejected prefixes and is bounded from L154; no arbitrary old choice program is bounded.',
'L182':'Deployment alias of L157; no second actual removal credit.'}
rows=[];diff=[]
for oldrow in base['rows']:
    r=copy.deepcopy(oldrow)
    if r['id'] in remove:
        diff.append(dict(**r,change='removed',reason=removed_reasons[r['id']]))
        continue
    r.update(status='retained',evidence='F3Y current root and fresh expanded inventories052–100; inherited Rc5 SAME-cut source/history outcome')
    if r['id']=='L159':
        r.update(running_job='SCC_',blocker='Retained exact frozen3 source-to-runtime StoredCarrierBinding at the SAME selected Rc5 dictionary. The fixture constructs one runtime, not the deployed arbitrary runtime instance.')
    if r['id'] in {'L165','L181','L185'}:
        r['blocker']='The charged frozen3 source/model transport is composed; complete physical runtime/deployed-event/source-to-ELF correspondence remains outside this theorem. No alias removal credit.'
    rows.append(r);diff.append(dict(**r,change='retained'))
# 7 pairing + 1 matching + 3 semantic + 1 dot + 1 canonical =13.
# These quantify over all source Evidence/At/Calls, not merely the retained
# native continuation. Identical row labels are NOT a domain-equivalence proof.
global_ids=[f'L{i:03}' for i in list(range(133,139))+list(range(142,149))]
assert len(global_ids)==13
oldby={r['id']:r for r in old['rows']}
for ident in global_ids:
    inherited=oldby['F3X_G_'+ident]
    r=dict(id='F3Y_G_'+ident,name=inherited['name'].replace('finishOwners.source_global.','finishOwners.source_global.'),
        classification='P',owner=inherited['owner'],scope='actual antecedent',status='added',running_job='SAG_',
        definition='lean/F3Y_PreparedAt.lean#Owners; lean/F3Y_FinishLeaves.lean#Holds',
        meaning=inherited['meaning'],evidence='F3Y_NewOwners/NewFinish kernel inventories; F3Y_Canonical/F3Y_Headline',
        blocker='Retained source-global family, distinct from Rc5 native-local witness/guard domain; no domain-equivalence or whole-source implementation instance is assumed proved.',
        owner_waits=['No owner decision pending'],
        disposition='Retained global finish family. Native counterpart '+ident+(' was removed locally by SAF, but this global canonicality family is still retained.' if ident=='L148' else ' remains separately counted.'))
    rows.append(r);diff.append(dict(**r,change='added'))

def count(rs):
    classes={k:Counter(r['classification'] for r in rs)[k] for k in ['T','P','C']}
    owners={o:{k:sum(r['owner']==o and r['classification']==k for r in rs) for k in ['T','P','C']} for o in ['lead','session A','external']}
    return dict(rows=len(rs),classes=classes,by_owner=owners)
actual=[r for r in rows if r['scope']=='actual antecedent']
deploy=[r for r in rows if r['scope']=='deployment only']
alias=[r for r in rows if r['scope']=='deployment alias']
counts={'actual antecedent':count(actual),'deployment only':count(deploy),'deployment alias':count(alias),
        'deduplicated actual plus non-alias deployment':count(actual+deploy),'all retained audit rows':count(rows),
        'actual excluding approved game domain':count([r for r in actual if not r['id'].startswith('Rc5_G')])}
assert counts['actual antecedent']['classes']=={'T':83,'P':43,'C':0},counts
assert counts['deduplicated actual plus non-alias deployment']['classes']=={'T':89,'P':56,'C':0},counts
assert len([r for r in actual if r['id'].startswith('Rc5_G')])==11
# Full F3X-to-current reconciliation, retaining failed/unavailable discharges.
chain={}
for n in [3,4,5]:
    x=json.loads((ROOT/f'evidence/recount{n}-20261026/Rc{n}_premises.json').read_text())
    for d in x['diff']:
        if d.get('change')=='removed':chain[d['id']]=dict(stage=f'Rc{n}',row=d)
current={r['id']:r for r in rows}
reconciliation=[]
for r in old['rows']:
    if r.get('status')=='removed':continue
    ident=r['id']
    if ident in current:
        disposition='retained with current native/game carrier';mapped=[ident];theorem='Rc5 source/history outcome preserved by F3Y_Headline'
    elif ident in chain:
        discharge=chain[ident];disposition='removed by inherited '+discharge['stage'];mapped=[ident]
        theorem=discharge['row'].get('theorem',discharge['row'].get('reason','see inherited row'))
    elif ident.startswith('F3X_G_'):
        local=ident.removeprefix('F3X_G_');mapped=[local]
        if local in {'L139','L140','L141'}:
            disposition='source-global family DERIVED; absent in actual new root'
            theorem='F3Y_PreparedScalars.values / FinishFields.from_fields / ReadModel.fields; native counterpart removed in Rc5 by SAF_C_SAF_FinishPrepared.strengthen'
        else:
            disposition='source-global family RETAINED as F3Y_G_'+local+'; NOT discharged by a native-local theorem'
            theorem=('Rc5 removed native-local L148 by accepted forward value transport (SAF_AcceptedValue), but that does not discharge arbitrary source-global canonicality.' if local=='L148' else 'Rc5 retains native-local '+local+'; F3Y retains separate source-global '+local)
    elif ident=='F3X_H_RuntimePersistence':
        disposition='same approved external runtime trust item, counted ONCE';mapped=['Rc5_T001'];theorem='CPR_DataPersistence.TwoTransactionLaw via CPG_History.on_cuts / Rc5_Close.from_saf'
    elif ident.startswith('F3X_H_'):
        name=ident.removeprefix('F3X_H_')
        maps={
          'entry1':(['Rc5_G002'],'game.a.entry1'),
          'positive':(['L083','Rc5_G002'],'CPG_Accepted.writer_positive'),
          'adjacent':(['Rc5_G001','Rc5_G006'],'CPH_Game.next'),
          'eligible':(['L083','Rc5_G002','Rc5_G004','Rc5_G005'],'CPG_Accepted.writer_ordinary; exact installed key law / CPH_Program.not_system'),
          'tentativeView':(['Rc5_G008','Rc5_G009','Rc5_G010'],'CPG_History.tentative_view / CPG_RuntimeTrace.result'),
          'status':(['Rc5_G007'],'game.c.parent'),
          'entry2View':(['L084','Rc5_G003','Rc5_G004'],'CPG_History.entry2_view / CPG_Accepted.reader_positive')}
        mapped,theorem=maps[name];disposition='old standalone history guard supplied/derived by approved SAME-cut Rc5 game; no extra guard added'
    else:
        raise AssertionError(('unmapped F3X row',ident))
    reconciliation.append(dict(id=ident,classification=r['classification'],scope=r['scope'],disposition=disposition,rc_chain_rows=mapped,theorem=theorem))
result=dict(actual_theorem='AspisR1.F3Y_Headline.deployed',baseline='AspisR1.Rc5_Top.deployed',
    baseline_path=str(basepath.relative_to(ROOT)),baseline_sha256=sha(basepath),before_counts=base['counts'],counts=counts,
    method='Reviewed atomic quantified-law-family correspondence, preserving guards/shared witness domains; fresh expanded kernel inventories. Not a solver or binder/structure count.',
    removed_actual_P=['L157','N117','N118'],removed_alias_P=['L182'],added_actual_P=['F3Y_G_'+i for i in global_ids],
    net_actual_P_delta=10,net_actual_T_delta=0,rows=rows,diff=diff,
    statement_evidence=evidence,unchanged_fresh_structure_inventories=sorted(unchanged),
    source_sha256={p.name:sha(p) for p in sorted((ROOT/'lean').glob('F3Y_*.lean'))},
    f3x_comparison=dict(before_actual=old['counts']['actual antecedent'],after_actual=counts['actual antecedent'],delta_T=0,delta_P=-148,
        original_171_to_191='171 -3 (L157,N117,N118) +16 global finish laws +7 standalone history guards =191; RuntimePersistence adds1T. These are scoped law families, not binder counts.',
        pending_credit='The three global claim/alpha0/alpha1 families are now actually removed at the checked new root.',
        current_composition='Rc5 native/history outcome replaces old Rc2 native/history outcome; old7 standalone guards are supplied by the same11 approved game clauses counted in Rc5. All13 remaining global finish families stay explicit.'),
    caveats=[
      '83T/33P ->83T/43P is a NET INCREASE of10P, despite three specific old rows removed. Do not report a net premise reduction.',
      'F3X83T/191P ->F3Y83T/43P includes inherited Rc3/Rc4/Rc5 work and changed approved game carriers; credit only three old-current rows and three global scalar derivations to this job.',
      '13 global finish laws are not silently deduplicated against12 native-local laws. Global L148 remains despite native L148 removal.',
      'L159 arbitrary deployed runtime carrier association remains; the non-vacuity theorem constructs one accepted recording instance only.',
      'The old independent native-account experiment is replaced by the SAME byte-prover account. No implication for arbitrary old adversary/chooseSecond carriers is asserted.',
      'Source extractor cost is cost OR SAME charged collision; model extraction/spend relation remain. No old unconditional source-cost conclusion is silently asserted.',
      'Focused coherent F3X/F3Y closure with unchanged pinned objects, not a package/full frozen-release replay; source-to-ELF gates remain.'])
(E/'F3Y_premises.json').write_text(json.dumps(result,indent=2)+'\n')
(E/'F3Y_field_catalog.json').write_text(json.dumps(catalog,indent=2)+'\n')
(E/'F3Y_F3X-reconciliation.json').write_text(json.dumps(reconciliation,indent=2)+'\n')
lines=['# F3Y current-headline atomic ledger','',
'Target not yet established unconditionally. This is reviewed law-family accounting, not a security percentage.','',
'| Scope | Rc5 before T/P | F3Y after T/P | Delta T/P |','|---|---:|---:|---:|',
'| Actual, including game and continuation guards |83/33|83/43|0/+10|',
'| Deduplicated actual plus deployment |89/46|89/56|0/+10|',
'| Actual excluding eleven approved game clauses |83/22|83/32|0/+10|','',
'Actual old-current removals: **L157,N117,N118**. Alias L182 gives no second credit. Added: **13 source-global finish law families**. No T or C row is discharged. Global claims/alpha0/alpha1 are derived by the checked authenticated-reader chain.','',
'BEFORE Rc5: exact selected dictionary, approved game/RuntimePersistence, accepted native wrappers, raw accepted source/model join, L159, byte-query and independent native-account budgets imply its native/history outcome and exact-source/model/account bounds.','',
'AFTER F3Y: same dictionary, game/runtime and native boundary; L159 and13 global finish laws, with SAME byte prover query budget, imply the SAME Rc5 native/history/physical-recorder conclusions, model extraction/spend relation, source cost OR the SAME account event, one charged runtime bound and exact positive zero-query margin. The independent old account experiment is replaced, not universally transported.','',
'F3X increase explained: **171−3+16+7=191P**, with RuntimePersistence adding1T. The16 families are six round laws, claim,alpha0,alpha1,pair,matching,three semantic equations,dot and canonicality. The7 guards are loaded TX1,positive CP,adjacency,ordinary eligibility,tentative source-bank image,parent success and loaded TX2 bytes. The key-law equality was already deduplicated at Rc2_P001.','',
'Current F3Y vs F3X: **83T/191P→83T/43P** (−148P). This incorporates the inherited Rc3–Rc5 discharges, the3 checked global scalar derivations and replacement of standalone history guards by the already-counted Rc5 game. It is not148 new discharges by this job.','',
'Every old actual/deployment row is mapped in F3Y_F3X-reconciliation.json. No mapping claims discharge of a retained global law merely because its native-local counterpart was removed. In particular, source-global canonicality remains; only its native-local counterpart L148 was removed by SAF.','',
'## Finish families and Rc-chain correspondence','',
'| F3X global row | Current disposition | Rc chain correspondence |','|---|---|---|']
for n in range(133,149):
    ident=f'L{n:03}';r=next(r for r in reconciliation if r['id']=='F3X_G_'+ident)
    lines.append('|'+ident+'|'+r['disposition']+'|'+r['theorem']+'|')
lines+=['','## History guards and Rc-chain correspondence','','| F3X item | Current rows | Supplying proof |','|---|---|---|']
for r in reconciliation:
    if r['id'].startswith('F3X_H_'):
        lines.append('|'+r['id']+'|'+','.join(r['rc_chain_rows'])+'|'+r['theorem']+'|')
lines+=['','## Remaining atomic rows','','| ID | Class | Owner | Scope | Meaning |','|---|---|---|---|---|']
for r in rows:lines.append('|'+r['id']+'|'+r['classification']+'|'+r['owner']+'|'+r['scope']+'|'+r['name']+'|')
(E/'F3Y_LEDGER.md').write_text('\n'.join(lines)+'\n')
print(json.dumps(dict(counts=counts,unchanged_inventories=len(unchanged),reconciled_rows=len(reconciliation)),indent=2))
