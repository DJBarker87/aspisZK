#!/usr/bin/env python3
"""PCUF_all.py: PCUF_ALL_STATUS.json, one record per reached (module, definition) over P5, P2a-d, P2r, P3a, P4a, P4c and P2f.
Selection rule (recorded in the file): a record has a CORRECT BASIS when its emission is not superseded (PCQF_SUPERSEDES) and its Aeneas configuration equals the
configuration required for the definition (ON for checked gate arithmetic; OFF where the gate body uses wrapping_* on plain operators, per the 2026-11-09 per-gate-module ruling,
applied per definition for modules that mix both). Authoritative = latest PROVED* record with a correct basis; else latest non-proved record with a correct basis; else the latest
record, flagged basis_not_correct. Conflicts (a different earlier/later status for the same definition) are listed."""
import json,re,sys,collections
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;EV=H.parent
RANK={'P2a':10,'P2d':11,'P5':20,'P4a':30,'P4c':31,'P2b':40,'P2c':41,'P2r':50,'P3a':60,'P2f':70}
SUP={"PCQC_E002","PCQC_E003","PCQC_E004","PCQC_E011","PCQ_E039","PCQ_E040"}
TOOL_B='aeneas-b59d5188-extended';TOOL_O='aeneas-original-959659a6'
def J(p): return json.load(open(EV/p))
recs=collections.defaultdict(list)
def add(module,defn,tool,status,**kw):
    r=dict(module=module,definition=defn,source=tool,rank=RANK[tool],status=status);r.update(kw);recs[(module,defn)].append(r)
def emission_of(s):
    runs=re.findall(r'(PCQC_E\d+|PCQF_E\d+|PCQE_E\d+|PCQ_E\d+|NMH_E\d+|NHR_E\d+|NMT_E\d+)',s or '')
    return runs
# ---- P2r / P2b / P2c (already per definition, with superseded_earlier_status for P2a/P2d)
PCUE=J('prov-p2r-20261109/PCUE_EQ_STATUS.json')['modules'];PCUB=J('prov-p2b-20261109/PCUB_EQ_STATUS.json')['modules'];PCUC=J('prov-p2c-20261109/PCUC_EQ_STATUS.json')['modules']
EARLIER_CFG={}
for m,v in PCUE.items():
    for n,r in v['reached'].items():
        s=r.get('superseded_earlier_status') or {}
        EARLIER_CFG[(m,n)]=s
        fr=r.get('fresh_source') or ''
        runs=emission_of(fr+json.dumps(r.get('fresh_run','')))
        add(m,n,'P2r',r['status'],theorem=r.get('theorem'),proving_file=('prov-p2r-20261109/PRVEq_'+r['pass_label']+'.lean') if r.get('pass_label') else None,fresh_emission=fr or None,emission_runs=runs,
            receipt=('prov-p2r-20261109/'+r['verify_attempt']+'/receipt.json') if r.get('verify_attempt') else None,configuration='ON',aeneas_tool=TOOL_B if runs and not any(x.startswith('PCQE') for x in runs) else None,note=r.get('reason') or r.get('error'))
for m,v in PCUB.items():
    for n,r in v['reached'].items():
        th=(r.get('theorems') or [{}])[0]
        fr=th.get('fresh_dir') or ((r.get('fresh') or [{}])[0].get('dir') if r.get('fresh') else None)
        runs=emission_of(json.dumps(th)+str(fr))
        add(m,n,'P2b',r['status'],theorem=th.get('theorem'),proving_file=('prov-p2b-20261109/PRVEq_'+th['label']+'.lean') if th.get('label') else None,fresh_emission=fr,emission_runs=runs,
            receipt=('prov-p2b-20261109/'+r['verify']+'/receipt.json') if r.get('verify') else None,configuration='ON',aeneas_tool=TOOL_B,note=r.get('reason'))
for m,v in PCUC.items():
    for n,r in v['reached'].items():
        fr=r.get('fresh_source');runs=emission_of(fr)
        add(m,n,'P2c',r['status'],theorem=r.get('theorem'),proving_file=('prov-p2c-20261109/PRVEq_'+m.replace('.','_')+r.get('pass_tag','')+'.lean') if r.get('theorem') else None,fresh_emission=fr,emission_runs=runs,
            receipt=('prov-p2c-20261109/'+r['verify_attempt']+'/receipt.json') if r.get('verify_attempt') else None,configuration='ON',aeneas_tool=TOOL_B,note=r.get('reason') or r.get('error'))
# ---- P2a / P2d from PCUA / PCUD, configuration from PCUE's superseded_earlier_status.fresh_overflow_on
for m,l in J('prov-p2a-20261109/PCUA_EQ_STATUS.json')['modules'].items():
    for r in l:
        n=r['gate_definition'];e=EARLIER_CFG.get((m,n),{})
        on=e.get('fresh_overflow_on')
        add(m,n,'P2a',r['status'],theorem=None,proving_file=('prov-p2a-20261109/'+r['generated_file']) if r.get('generated_file') else None,fresh_emission=r.get('fresh_emission'),emission_runs=emission_of(r.get('fresh_emission')),
            receipt=('prov-p2a-20261109/PCUA_'+r['final_scope']+'/receipt.json') if r.get('final_scope') else None,configuration=('ON' if on else 'OFF' if on is False else 'UNKNOWN'),aeneas_tool=TOOL_B if 'prov-p1b' in str(r.get('fresh_emission')) else 'retained NMH/NHR emission (tool per its receipt)',note=r.get('reason') or r.get('first_failing_goal_or_error'))
PCUD=J('prov-p2d-20261109/PCUD_EQ_STATUS.json')['modules']
for m,v in PCUD.items():
    for n,r in v['reached'].items():
        e=EARLIER_CFG.get((m,n),{});on=e.get('fresh_overflow_on')
        add(m,n,'P2d',r['status'],theorem=r.get('theorem'),proving_file=('prov-p2d-20261109/PRVEq_'+m.replace('.','_')+r.get('pass_tag','')+'.lean') if r['status'].startswith('PROVED') else None,fresh_emission=r.get('fresh_source') or e.get('fresh'),
            emission_runs=emission_of(str(r.get('fresh_source'))),receipt=('prov-p2d-20261109/'+r['verify_attempt']+'/receipt.json') if r.get('verify_attempt') else None,
            configuration=('ON' if on else 'OFF' if on is False else 'UNKNOWN'),aeneas_tool='retained NMH/NHR/NKM/NMT emission (tool per its receipt)',note=r.get('reason') or r.get('error'))
# ---- P5
PCT=J('prov-p5-20261109/PCT_STATUS.json')['modules']
for m,v in PCT.items():
    for n,r in v['reached'].items():
        fr=None
        add(m,n,'P5',r['status'],theorem=r.get('theorem'),proving_file=('prov-p5-20261109/PRVEq_'+m.replace('.','_')+r.get('pass_tag','')+'.lean') if r.get('theorem') else None,
            fresh_emission='receipted retained emission or FILE: source of the a-lane module (PCT_STATUS passes)',emission_runs=[],receipt=('prov-p5-20261109/'+r['attempt']+'/receipt.json') if r.get('attempt') else None,
            configuration='UNKNOWN',aeneas_tool='receipted NMH/NHR/NKM emission (tool per its receipt)',note=r.get('reason'))
# ---- P4a (per definition from the generated states; module labels are the P4a file stems)
for f in sorted((EV/'prov-p4a-20261109/eq').glob('PRVEq_*.state2.json')):
    stem=f.name[len('PRVEq_'):-len('.state2.json')];s=json.load(open(f))
    for n,x in s['defs'].items():
        add(stem,n,'P4a','PROVED_RFL' if x.get('status')=='proved' and x.get('stage')==1 else 'PROVED_UNFOLD' if x.get('status')=='proved' else 'FAILED',theorem='PRVEq.'+stem+'.'+n,proving_file='prov-p4a-20261109/eq/PRVEq_'+stem+'.lean',
            fresh_emission='PCWA_E0nn (see PCWA_STATUS.json module entry)',emission_runs=[],receipt='prov-p4a-20261109/PCWA_L009..L011/receipt.json (PCWA_STATUS.json equalities.lean_scope)',configuration='ON',aeneas_tool=TOOL_B,note='P4a reference/cut module; module label = generated file stem; granularity: definition',definition_relative=True)
# ---- P3a
reached_u=collections.defaultdict(list)
for (m,n) in list(recs): reached_u[m].append(n)
unmatched=[]
for it in J('prov-p3a-20261109/PCVA_CLASSIFICATION.json')['items']:
    m=it['module'];names=[x.strip() for x in re.split(r',\s*|\s+\(|\)',it['definition']) if x.strip()]
    hit=0
    for rel in names:
        rel=rel.split(' ')[0]
        for n in reached_u.get(m,[]):
            if it['status']=='PROVED_CONDITIONAL_ON_H_P' and 'pair_forest_accounts' not in n: continue   # the H_P item concerns pair_forest_accounts only
            if n==rel or n.endswith('.'+rel):
                add(m,n,'P3a',{'PROVED':'PROVED_P3','NOT_PROVED':'NOT_PROVED_P3','PROVED_CONDITIONAL_ON_H_P':'PROVED_CONDITIONAL_ON_H_P','NOT_ATTEMPTED':'NOT_ATTEMPTED_P3'}[it['status']],theorem=None,proving_file=('prov-p3a-20261109/'+it['file']) if it.get('file') else None,
                    fresh_emission='inherited from the underlying P2/P5 record of the same definition',emission_runs=[],receipt=('prov-p3a-20261109/'+it['verify_attempt']+'/receipt.json') if it.get('verify_attempt') else None,configuration='INHERIT',aeneas_tool='inherited',note=it['classification']+': '+it['note'][:300]);hit+=1
    if not hit: unmatched.append(dict(module=m,definition=it['definition'][:200],status=it['status'],file=it.get('file'),note='definition names not matched to a reached definition of the module; item-level record kept in module_level'))
# ---- P2f (EQ_STATUS)
PCUF=J('prov-p2f-20261109/PCUF_EQ_STATUS.json')
for m,v in PCUF['modules'].items():
    for n,r in v['reached'].items():
        if r.get('carried_from') and r['status']==r['supersedes']['status']: continue   # unchanged carried records are the earlier P2b/P2c/P2r records themselves
        add(m,n,'P2f',r['status'],theorem=r.get('theorem'),proving_file=('prov-p2f-20261109/'+r['theorem_file']) if r.get('theorem_file') else None,fresh_emission=r.get('fresh_source'),emission_runs=[r.get('fresh_run')],
            receipt=('prov-p2f-20261109/'+r['verify_attempt']+'/receipt.json') if r.get('verify_attempt') else None,configuration=r.get('configuration','ON'),aeneas_tool=r.get('aeneas_tool'),note=r.get('error') or r.get('config_mismatch_reason'))
# P2f P3 loop refinement (item 2): replaces the H_P-conditional P3a result
HP=[('AspisR1TerminalDecoder.Funs','AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop.body'),('AspisR1TerminalDecoder.Funs','AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical_loop'),
    ('AspisR1TerminalDecoder.Funs','AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.digest_is_canonical'),('AspisR1TerminalDecoder.Funs','AspisR1TerminalDecoder.pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1')]
THM={'digest_is_canonical_loop.body':'PRVP3f.body_refines (+ body_cont)','digest_is_canonical_loop':'PRVP3f.loop_refines','digest_is_canonical':'PRVP3f.digest_is_canonical_eq','pool_v1_pair_forest_output_lane_v1':'PRVP3f.output_lane_eq'}
for m,n in HP:
    key=[k for k in THM if n.endswith(k)][-1] if any(n.endswith(k) for k in THM) else None
    k2=max([k for k in THM if n.endswith(k)],key=len)
    add(m,n,'P2f','PROVED_P3_LOOP_REFINEMENT',theorem=THM[k2]+' ; PRVP3f.P_eq',proving_file='prov-p2f-20261109/PRVEq_TD_HP_P3f.lean',fresh_emission='prov-p1e-20261109/PCQF_E002_emitted (S009 re-run, aspis_core.field.P transparent)',emission_runs=['PCQF_E002'],
        receipt='prov-p2f-20261109/PCUF_L015/receipt.json',configuration='ON',aeneas_tool=TOOL_B,note='statement is a refinement (fresh Option Bool loop-return = gate Bool loop), not a plain equality; no hypothesis H_P; callee atomic_statement.encode_digest_canonical resolved by name to the gate constant (output_lane_eq)')
# ---- consolidate
REQ_OFF=set()
for (m,n),l in recs.items():
    for r in l:
        if r['status']=='CONFIG_MISMATCH': REQ_OFF.add((m,n))
def required(m,n): return 'OFF' if (m,n) in REQ_OFF else 'ON'
def basis_ok(r,req):
    reasons=[]
    if any(x in SUP for x in (r.get('emission_runs') or [])): reasons.append('emission superseded by PCQF_SUPERSEDES.json')
    c=r['configuration']
    if c in('ON','OFF') and c!=req: reasons.append(f'configuration {c} != required {req}')
    if c=='UNKNOWN': reasons.append('configuration of the compared emission not established (receipted/retained emission)')
    return reasons
out={};conf=[];tot=collections.Counter();by_src=collections.Counter()
for (m,n),l in sorted(recs.items()):
    req=required(m,n)
    l=sorted(l,key=lambda r:r['rank'])
    # P3a inherits configuration/emission from the latest non-P3a record of the same definition
    base=[r for r in l if r['source']!='P3a' and r['source']!='P2f']
    for r in l:
        if r['source']=='P3a':
            b=base[-1] if base else None
            r['configuration']=b['configuration'] if b else 'UNKNOWN';r['emission_runs']=b['emission_runs'] if b else [];r['inherits_from']=b['source'] if b else None
    for r in l: r['basis_problems']=basis_ok(r,req)
    P=lambda r:r['status'].startswith('PROVED')
    good=[r for r in l if not r['basis_problems']]
    pick=([r for r in good if P(r)] or [r for r in good if not P(r)] or [])
    if pick: auth=max(pick,key=lambda r:r['rank']);bn=False
    else:
        pp=[r for r in l if P(r)] or l;auth=max(pp,key=lambda r:r['rank']);bn=True
    # CONFIG_MISMATCH with a correct-basis OFF proof is resolved by the OFF proof (already handled: required()==OFF excludes ON records)
    if req=='OFF' and bn and not P(auth):
        auth=dict(auth);auth['status']='CONFIG_MISMATCH_NO_OFF_RESULT';auth['note']=(auth.get('note') or '')+' | required configuration OFF (gate body uses wrapping operators); no OFF emission of this definition with a correct-basis result exists'
    final=dict(module=m,definition=n,status=auth['status'],theorem=auth.get('theorem'),proving_file=auth.get('proving_file'),fresh_emission=auth.get('fresh_emission'),receipt=auth.get('receipt'),
               configuration=auth['configuration'],required_configuration=req,aeneas_tool=auth.get('aeneas_tool'),decided_by=auth['source'],basis_not_correct=bn,basis_problems=auth['basis_problems'],note=auth.get('note'),
               supersedes=[dict(source=r['source'],status=r['status'],fresh_emission=r.get('fresh_emission'),configuration=r['configuration'],basis_problems=r['basis_problems']) for r in l if r is not auth])
    ss={r['status'] for r in l}
    if len({(r['status'].startswith('PROVED')) for r in l})>1:
        conf.append(dict(module=m,definition=n,resolved_to=auth['status'],decided_by=auth['source'],records=[(r['source'],r['status'],r['configuration'],r['basis_problems']) for r in l]))
    out.setdefault(m,{})[n]=final;tot[final['status']]+=1;by_src[final['decided_by']]+=1
Path(H/'PCUF_ALL_STATUS.json').write_text(json.dumps(dict(schema='PCUF_ALL_STATUS/1',target_established=False,selection_rule=__doc__,
  sources=sorted(RANK),totals=dict(tot),decided_by=dict(by_src),n_modules=len(out),n_definitions=sum(len(v) for v in out.values()),n_conflicts=len(conf),conflicts=conf,
  module_level={'P4c':'evidence/prov-p4c-20261109/PCWC_STATUS.json items T,D3,S1,S2,S3,S4,N,A: tool build, S1 meaning, archive reproductions and the NJT_claims_ref Funs equalities (5/5 rfl, PCWC_L004) are module-level; P4c produced no definition list in the reached sets of this table',
                'P3a_unmatched_items':unmatched,'P4a_note':'P4a module labels are generated-file stems (relative definition names)'},modules=out),indent=0))
print(dict(tot),len(out),sum(len(v) for v in out.values()),len(conf))
