#!/usr/bin/env python3
"""PCUH_all.py: PCUH_ALL_STATUS.json (consolidated, one record per reached definition), PCUH_NONFROZEN_STATUS.json, PCUH_REMAINING.json.
Base = PCUG_ALL_STATUS.json (P2a..P2g, P3a, P4a, P4c module level, P5). Definition universe also includes the PCXA_PROVENANCE definitions
(RECEIPTED markers, P4b/P4c audited lists). Overlays in order: P3b (PCVB_NONFROZEN_STATUS), P3c (PCVC_STATUS), P3d (PCVD_STATUS), P4e (PCWE_STATUS), P2h (this job).
Every status change against the previous winner is listed in `conflicts_resolved`."""
import json,re,sys,collections,copy
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;EV=H.parent
def J(p): return json.load(open(EV/p))
base=J('prov-p2g-20261109/PCUG_ALL_STATUS.json'); pcxa=J('prov-p6s-20261109/PCXA_PROVENANCE.json')
nf=J('prov-p3b-20261109/PCVB_NONFROZEN_STATUS.json'); pvc=J('prov-p3c-20261109/PCVC_STATUS.json'); pvd=J('prov-p3d-20261109/PCVD_STATUS.json')
pwe=J('prov-p4e-20261109/PCWE_STATUS.json'); rem_d=J('prov-p3d-20261109/PCVD_REMAINING.json'); eq=J('prov-p2h-20261109/PCUH_EQ_STATUS.json')
cov=J('prov-p1g-20261109/PCQD_COVERAGE.json'); nofz=J('prov-p1g-20261109/PCQD_NO_FROZEN_COUNTERPART.json')
PROVED={'PROVED_RFL','PROVED_UNFOLD','PROVED_EQUIV','PROVED_P3','PROVED','EQUALITY_PROVED'}
def norm(raw,basis_bad,pcxa_status,note=''):
    if raw in PROVED and not basis_bad: return 'EQUALITY_PROVED',None
    if raw=='PROVED_P3_LOOP_REFINEMENT' and not basis_bad: return 'EQUALITY_DOMAIN','loop-return refinement (Option Bool vs Bool), not a plain equality'
    if raw in PROVED and basis_bad: return 'OPEN','WRONG_BASIS (configuration of the compared emission does not match the required one; counts OPEN per 2026-11-09 ruling)'
    if pcxa_status=='RECEIPTED': return 'RECEIPTED',None
    return 'OPEN',f'{raw}'+(': '+note if note else '')
mods={}
conflicts=[]
def put(m,d,rec): mods.setdefault(m,{})[d]=rec
for m,ds in base['modules'].items():
    for d,r in ds.items():
        px=(pcxa['modules'].get(m,{}).get('definitions',{}).get(d,{}) or {})
        fs,why=norm(r['status'],r.get('basis_not_correct'),px.get('status'),r.get('note') or '')
        rec=dict(module=m,definition=d,status=fs,open_reason=why,base_status=r['status'],theorem=r.get('theorem'),proving_file=r.get('proving_file'),
                 fresh_emission=r.get('fresh_emission'),receipt=r.get('receipt'),configuration=r.get('configuration'),required_configuration=r.get('required_configuration'),
                 aeneas_tool=r.get('aeneas_tool'),source_revision='frozen 4bb3b3f (fresh emission) vs gate module source (non-frozen where listed in PCUH_NONFROZEN_STATUS)',
                 decided_by=r.get('decided_by'),supersedes=(lambda x: x if isinstance(x,list) else ([x] if x else []))(r.get('supersedes')),pcxa_status=px.get('status'))
        if px.get('status')=='RECEIPTED' and fs=='OPEN' and r['status'] in('NOT_COVERED','NO_FRESH_EMISSION','TEXT_ONLY_NOT_COMPARED'):
            rec['status']='RECEIPTED'; rec['open_reason']=None
        put(m,d,rec)
# definitions only in PCXA
for m,mv in pcxa['modules'].items():
    for d,px in mv.get('definitions',{}).items():
        if d not in mods.get(m,{}):
            put(m,d,dict(module=m,definition=d,status=px['status'] if px['status'] in('RECEIPTED','EQUALITY_PROVED','EQUALITY_DOMAIN') else 'OPEN',open_reason=px.get('open_reason'),base_status=None,
                 theorem=None,proving_file=None,fresh_emission=None,receipt=None,configuration=px.get('configuration'),required_configuration=px.get('required_configuration'),
                 aeneas_tool=px.get('aeneas_tool'),source_revision='frozen 4bb3b3f',decided_by='PCXA',supersedes=[],pcxa_status=px['status'],origin_only='PCXA_PROVENANCE'))
def setstatus(m,d,new,why,phase,**kw):
    r=mods.get(m,{}).get(d)
    if r is None:
        r=dict(module=m,definition=d,status=new,open_reason=None,base_status=None,theorem=None,proving_file=None,fresh_emission=None,receipt=None,configuration=None,required_configuration=None,
               aeneas_tool=None,source_revision='frozen 4bb3b3f',decided_by=phase,supersedes=[],origin_only=phase+' (not in the P2g/PCXA universe)'); put(m,d,r)
    if r['status']!=new: conflicts.append(dict(module=m,definition=d,from_status=r['status'],to_status=new,phase=phase,reason=why))
    r['supersedes']=(r.get('supersedes') if isinstance(r.get('supersedes'),list) else [])+[dict(status=r['status'],decided_by=r.get('decided_by'),theorem=r.get('theorem'))]
    r['status']=new; r['open_reason']=(None if new in('EQUALITY_PROVED','RECEIPTED','EQUALITY_DOMAIN') else why); r['decided_by']=phase; r.update(kw)
def find(m,short):
    short=re.split(r'[\s(]',short.strip())[0]
    ks=[k for k in mods.get(m,{}) if k==short or k.endswith('.'+short)]
    return ks
# --- P3b overlay: the PCVB table itself (R72 Funs overlay + gate-only helper behaviours)
for m,mv in nf['modules'].items():
    for d,r in mv['definitions'].items():
        if r['status']=='EQUALITY_PROVED' and d in mods.get(m,{}) and mods[m][d]['status'] not in('EQUALITY_PROVED','EQUALITY_DOMAIN') and r.get('file','') and 'P3' in (r.get('file') or ''):
            setstatus(m,d,'EQUALITY_PROVED','P3b R72 overlay','P3b',theorem=r.get('theorem'),proving_file=r.get('file'))
        if r['status'].startswith('GATE_ONLY_HELPER') and d in mods.get(m,{}):
            setstatus(m,d,'NO_FROZEN_COUNTERPART','gate-only helper; behaviour proved (P3b), no frozen function to equate','P3b',theorem=r.get('theorem'),proving_file=r.get('file'))
# --- P3c, P3d overlays
unmatched=[]
for phase,recs in (('P3c',pvc['proved_or_discharged']),('P3d',pvd['proved_records'])):
    for r in recs:
        m=r['module']; ks=find(m,r['definition'])
        if not ks: unmatched.append(dict(phase=phase,module=m,definition=r['definition'],result=r.get('result'),file=r.get('file'),why='definition name not matched to a reached definition of the module')); continue
        cls=r.get('classification')
        if cls=='CONSTANT_BINDING' or 'INSTANCE_TRANSPORT' in (cls or ''):
            new,why='CONDITIONAL_ON_BINDING',('constant binding (external := ok <gate/fresh value>)' if cls=='CONSTANT_BINDING' else 'parametric transport over an opaque external; consumer instantiation not proved')
        elif cls=='GENERIC_LEMMA': continue
        else: new,why='EQUALITY_PROVED',None
        for k in ks:
            if mods[m][k]['status']=='EQUALITY_DOMAIN' and new=='EQUALITY_PROVED': mods[m][k].setdefault('notes',[]).append(f'{phase}: SOURCE_SHAPE record kept as EQUALITY_DOMAIN (loop-return refinement, not a plain equality)'); continue
            setstatus(m,k,new,why or '',phase,theorem=(r.get('theorem') or (r.get('theorems') or [None])[0]),proving_file=r.get('file'),p3_class=cls)
# --- P3d remaining items (open categories)
for it in rem_d['items']:
    m,d=it['module'],it['definition']; ks=[d] if d in mods.get(m,{}) else find(m,d.split('.',1)[-1] if '.' in d else d)
    for k in ks:
        r=mods[m][k]
        if r['status']=='OPEN': r['p3d_open_category']=it['category']; r['open_reason']=(r['open_reason'] or '')+f' | P3d: {it["category"]}'
# --- P4e overlay (cut modules ties reproduced archive text to the gate; flagged)
for m,mv in pwe['modules'].items():
    for d,x in (mv.get('definitions') or {}).items():
        ks=[d] if d in mods.get(m,{}) else find(m,d)
        for k in ks:
            if x.get('status')=='PROVED' and mods[m][k]['status']!='EQUALITY_PROVED':
                setstatus(m,k,'EQUALITY_PROVED','P4e: reproduced archive text = gate (cut-module equality; not archive crate = frozen source)','P4e',theorem=f'PRVEq.{m}.{d}',proving_file=mv.get('equality_file'),
                          cut_module_archive_only=True,substitute_tool=('CircleSampleWrapper: unpatched Aeneas 959659a6 on the archived LLBC (flagged, not a reproduction)' if 'CircleSample' in m else None))
# --- P2h overlay (this job)
EQ={}
for r in eq['records']:
    if r['kind']=='type' and r['status']!='EQUALITY_PROVED': pass
    EQ[(r['module'],r['definition'])]=r
changed=0
for (m,d),r in EQ.items():
    # gate-name matching: P2h definition = gate namespace + relative name; the module tables use gate-relative or namespaced names
    cands=[d,d.split('.',1)[-1]] if '.' in d else [d]
    k=next((c for c in cands if c in mods.get(m,{})),None)
    if k is None:
        # search by suffix
        ks=[x for x in mods.get(m,{}) if d.endswith('.'+x) or x.endswith('.'+d.split('.',1)[-1])]
        k=ks[0] if len(ks)==1 else None
    kw=dict(theorem=r.get('theorem'),proving_file=r.get('proving_file'),receipt=r.get('verifying_scope'),fresh_emission=r.get('fresh_run')+' '+str(r.get('fresh_dir')),aeneas_tool=r.get('aeneas_tool'),
            configuration=r.get('configuration_fresh'),required_configuration=r.get('required_configuration'),
            config_bridge=bool(r.get('gate_requires_wrapping_ops') and r['status']=='EQUALITY_PROVED'),given_block=r.get('given'))
    if r['status']=='EQUALITY_PROVED':
        newk=k or d
        setstatus(m,newk,'EQUALITY_PROVED','P2h','P2h',**kw); changed+=1
    else:
        newk=k or d
        cls={'HAND_ADAPTED':'HAND_ADAPTED'}.get(r.get('reason_class'),'OPEN')
        why=f"{r.get('reason_class')}: {r.get('reason','')[:160]}"
        cur=mods.get(m,{}).get(newk)
        if cur is not None and cur['status'] in('EQUALITY_PROVED','RECEIPTED'): cur['p2h_attempt']=dict(outcome=cls,reason=why,label=r.get('label'),note='P2h equality attempted against the frozen emission and not proved; the existing status is kept')
        if cur is None or cur['status'] not in('EQUALITY_PROVED','RECEIPTED'):
            setstatus(m,newk,cls,why,'P2h',**{k2:v for k2,v in kw.items() if k2 in('fresh_emission','aeneas_tool','configuration','required_configuration')})
# --- binding upgrades (item 4): the constants' own transparent fresh definition (PCQF_E007) = the gate constant, PRVEq_const_bind.lean, PCUH_L037
UP=[('QM31.ZERO/ONE','PRVEq.const.QM31_ZERO/QM31_ONE (limbwise)'),('FIq M31.ONE/ZERO','PRVEq.const.M31_ONE_FIq / M31_ZERO_FIq'),('NEW_GeometryActual M31.ONE/ZERO','PRVEq.const.M31_ONE / M31_ZERO')]
upgraded=[]
for m,ds in mods.items():
    for d,r in ds.items():
        if r['status']=='CONDITIONAL_ON_BINDING' and r.get('p3_class')=='CONSTANT_BINDING':
            pass
for rec in pvd['proved_records']:
    if rec.get('classification')!='CONSTANT_BINDING': continue
    inst=rec.get('instantiation') or ''
    if 'STATE_ONLY_HIDING' in inst: continue
    ks=find(rec['module'],rec['definition'])
    for k in ks:
        r=mods[rec['module']][k]
        if r['status']=='CONDITIONAL_ON_BINDING':
            used='QM31' if 'QM31' in inst else 'M31.ONE'
            r['status']='EQUALITY_PROVED'; r['open_reason']=None
            r['binding_upgrade']=dict(constants=used,proof='PRVEq_const_bind.lean '+('PRVEq.const.QM31_ZERO/QM31_ONE' if used=='QM31' else 'PRVEq.const.M31_ONE_FIq'),scope='PCUH_L037',
                 remaining='the link external axiom X : Result T = ok <transparent aspis_core value> is a property of how Aeneas types cross-crate constants (FunsExternal_Template), now bound to the fresh transparent definition whose value equals the gate constant')
            upgraded.append(dict(module=rec['module'],definition=k,constants=used)); conflicts.append(dict(module=rec['module'],definition=k,from_status='CONDITIONAL_ON_BINDING',to_status='EQUALITY_PROVED',phase='P2h',reason='constant upgrade (PRVEq_const_bind.lean)'))
# NFN line_node (P2h) used the NEW_GeometryActual M31.ONE binding
for lab in ('NFN_ExtractedGeometry','NFN_ExtractedGeometry_p2'):
    pass
# totals + file output
tot=collections.Counter(r['status'] for ds in mods.values() for r in ds.values())
rem=collections.defaultdict(list)
for m,ds in mods.items():
    for d,r in ds.items():
        if r['status'] in('OPEN','CONDITIONAL_ON_BINDING','HAND_ADAPTED','NO_FROZEN_COUNTERPART'): rem[r['status']].append(dict(module=m,definition=d,reason=r.get('open_reason'),p3d=r.get('p3d_open_category')))
out=dict(schema='PCUH_ALL_STATUS/1',target_established=False,rule=base['selection_rule'],
  statuses='RECEIPTED | EQUALITY_PROVED | CONDITIONAL_ON_BINDING | EQUALITY_DOMAIN | OPEN (open_reason) | HAND_ADAPTED | NO_FROZEN_COUNTERPART',
  sources=['PCUG_ALL_STATUS.json (P2a-P2g, P3a, P4a, P4c module-level, P5)','PCXA_PROVENANCE.json (RECEIPTED markers; P4b/P4c audited lists)','PCVB_NONFROZEN_STATUS.json (P3b)','PCVC_STATUS.json (P3c)','PCVD_STATUS.json (P3d)','PCWE_STATUS.json (P4e)','PCUH_EQ_STATUS.json (P2h)','PRVEq_const_bind.lean (P2h item 4)'],
  excluded_from_credit=['PRVC_N02_exp* (scratch with sorry)','PCVB_L025/L030/L031 probe copies and any file containing sorry','P2h probe files PRVEq_probe1.lean/probe3.lean (sorry; deleted, receipt source copies of PCUH_L001/L022/L023 removed)','PCUH_L002-L009 failed PRVH_WrapAdd intermediates and PCUH_L012/L013 order probes (errors)'],
  p4b_note='P4b/P4c: definitions are those of the PCXA_L009/L010 audited theorem lists as merged in PCXA_PROVENANCE; PCWB_STATUS.json (P4b) lists cut-module triage and was not re-audited here',
  n_modules=len(mods),n_definitions=sum(len(v) for v in mods.values()),totals=dict(tot),n_conflicts_resolved=len(conflicts),conflicts_resolved=conflicts,unmatched_p3_records=unmatched,
  binding_upgrades=upgraded,modules=mods)
json.dump(out,open(H/'PCUH_ALL_STATUS.json','w'),indent=1)
json.dump(dict(schema='PCUH_REMAINING/1',target_established=False,counts={k:len(v) for k,v in rem.items()},items=rem,
   not_established=['TerminalDecoder pair_terminal / pair_tree_profile (6 EXTERNAL_P records): the only emissions containing them type field.P as an opaque axiom; P1g produced none (PCQD_FAILURES: boxed decoders failed on both tools)',
    'FIo_Native mul_by_r, heap.filled, Dot.push, FIp four_dots* (NONFROZEN_WAIT_P1G): no new emission in P1g; not attempted',
    'Native13 COPY_PATTERNS literal (200-line) fresh = gate: retired shape, still an open obligation',
    'Native07 STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS binding: no transparent fresh emission located',
    'config mismatches (gate wrapping vs fresh checked) without an overflow-freedom argument: NJA_CountBody (6), NFN closure call_mut (5*i + k), reachability of the closure domain not shown']),
  open(H/'PCUH_REMAINING.json','w'),indent=1)
print(dict(tot),len(conflicts),len(unmatched),len(upgraded))
