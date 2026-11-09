#!/usr/bin/env python3
"""PCUE_final.py: PCUE_EQ_STATUS.json, PCUE_FOR_P3.json from the final states. One record per reached definition of every P2a/P2d module."""
import json,re,sys,difflib,glob
from pathlib import Path
sys.dont_write_bytecode=True
import PCUE_gen_equalities as G, PCUE_plan as PL, PCUE_match as M
H=Path(__file__).resolve().parent;EV=H.parent
PLAN=json.load(open(H/'PCUE_PLAN.json'));SD=M.SD
P=PL.P
OK_AX={'propext','Classical.choice','Quot.sound'}
OV=re.compile(r'wrapping_|checked_|overflowing_|saturating_')
def label(m,ps): return m.replace('.','_')+ps['tag']
bundles=json.load(open(H/'gen/bundles.json'))
VER=json.load(open(H/'gen/verify_attempts.json'))   # {bundle key: attempt id}
lab2v={}
for bk,att in VER.items():
    for l in bundles[bk]: lab2v[l]=(bk,att)
AX={}
for bk,att in VER.items():
    r=json.load(open(H/att/'receipt.json'))
    AX[bk]=dict(attempt=att,target=r['module'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],axioms=' '.join(' '.join(r['print_axioms']).split()))
def overflow_on(d):
    if d is None or d.startswith('FILE:'): return False
    d=Path(d);base=EV.parent/d if not d.is_absolute() else d
    for up in (base,base.parent,base.parent.parent):
        c=up/'charon_receipt.json'
        if c.exists(): return 'overflow-checks=yes' in c.read_text()
    return False
def old_info(m,full):
    st,tool,fe=SD[m][full]
    # P2a stores the fresh emission per definition; P2d per pass (use the pass whose covers include it)
    if tool=='P2d':
        pr=json.load(open(EV/'prov-p2d-20261109/PCUD_EQ_STATUS.json'))['modules'][m]
        fs=[p['fresh_dir'] for p in pr['passes'] if full in p['covers']]
        fe=fs[0] if fs else None
    return dict(tool=tool,status=st,fresh=fe,fresh_overflow_on=overflow_on(fe) if fe else None)
def blocks(path): return {b['name']:b for b in G.parse_blocks(Path(path).read_text()) if b['kind']=='decl'}
def toks(b): return G.norm_decl(b).split()
def opdiff(fb,gb):
    a,b=toks(fb),toks(gb);sm=difflib.SequenceMatcher(a=a,b=b,autojunk=False)
    return [(a[i1:i2],b[j1:j2]) for t,i1,i2,j1,j2 in sm.get_opcodes() if t!='equal']
def udiff(fb,gb,limit=1800):
    d=list(difflib.unified_diff(toks(fb),toks(gb),'fresh','gate',n=2,lineterm=''));return ' '.join(d[2:])[:limit]
def latest_state(lab):
    for k in (3,2,1):
        p=H/f'gen/PRVEq_{lab}.state{k}.json'
        if p.exists(): return json.load(open(p)),k
    return None,0
out={};p3=[];tot={};hand=[]
for m,defs in SD.items():
    pl=PLAN.get(m)
    recs={}
    if pl is None: continue
    gns=pl.get('gate_ns')
    for full in defs:
        recs[full]=None
    for ps in pl['passes']:
        lab=label(m,ps);st,rnd=latest_state(lab)
        if st is None: continue
        g,q,_o=PL.gate_sources(m);gb={b['name']:b for b in G.parse_blocks(g) if b['kind']=='decl'}
        fp=EV/ps['fresh_dir']/('Types.lean' if ps['kind']=='Types' else 'Funs.lean');fb={b['name']:b for b in G.parse_blocks(fp.read_text()) if b['kind']=='decl'}
        nm=ps.get('name_map',{})
        vk=lab2v.get(lab)
        for n,x in st['defs'].items():
            gn=nm.get(n,n);full=gns+'.'+gn
            if full not in recs: continue
            thm=f"PRVEq.{m}{ps['tag']}.{n}"
            base=dict(pass_label=lab,theorem=thm,fresh_source=ps['fresh_dir'],fresh_run=ps['run'],fresh_overflow_checks_on=True,fresh_name=n,gate_source=pl['gate_origin'],statement=f"@{gns}.PRVFresh_{lab}.{n} = @{gns}.{gn}",
                      verify_bundle=vk[0] if vk else None,verify_attempt=vk[1] if vk else None,state_round=rnd)
            if x['status']=='proved':
                dk='structure-equiv' if x.get('callees') is not None and fb.get(n,{}).get('dkind')=='structure' else fb.get(n,{}).get('dkind')
                stt='PROVED_EQUIV' if fb.get(n,{}).get('dkind')=='structure' else ('PROVED_RFL' if x['stage']==1 else 'PROVED_UNFOLD')
                ent=dict(base,status=stt)
                a=AX.get(vk[0],{}).get('axioms','') if vk else ''
                mm=re.search(r"'"+re.escape(thm)+r"(?:\.equiv)?' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",a)
                if mm:
                    axs=set(z.strip() for z in (mm.group(2) or '').split(',') if z.strip());ent['axioms']=sorted(axs);ent['axioms_ok']=axs<=OK_AX
                else: ent['axioms']='NOT_FOUND_IN_VERIFY_RECEIPT';ent['axioms_ok']=None
            else:
                ent=dict(base,status='FAILED',failure_class=x.get('class'),error=(x.get('error') or '')[:400],callees=x.get('callees'))
                if n in fb and gn in gb:
                    ent['diff_normalized']=udiff(fb[n],gb[gn]);ops=opdiff(G_ren(fb[n]) if False else fb[n],gb[gn]);ent['body_identical_modulo_name_map']=None
                    ent['_ops']=ops
                    ent['fresh_body']=G.norm_decl(fb[n])[:2500];ent['gate_body']=G.norm_decl(gb[gn])[:2500]
            cur=recs[full]
            if cur is None or (ent['status'].startswith('PROVED') and not cur['status'].startswith('PROVED')): recs[full]=ent
        # covered but not generated (not common, e.g. types text-only)
    for full in list(recs):
        if recs[full] is not None: continue
        old=old_info(m,full)
        if pl['status'].startswith(('GATE_SOURCE','GATE_MULTI')):
            rel=full.split('.',1)[1] if '.' in full else full
            hit=[(ent['run'],k) for e_,ent in PL.idx.items() for k in ('Types','Funs') for v in PL.variants(rel) if v in ent.get(k,{})]
            recs[full]=dict(status='GATE_SOURCE_UNAVAILABLE',reason='gate source for this module is not a single-namespace file the generator accepts ('+pl['status']+'); no Lean statement generated',
                            overflow_on_name_present_informational=sorted(set(hit)) or None)
        else:
            covered=any(full[len(gns)+1:] in ps['covers'] for ps in pl['passes']) if gns else False
            if covered: recs[full]=dict(status='TEXT_ONLY_NOT_COMPARED',reason='overflow-checks-on emission declares the name but the generator emits no equality for this declaration shape (inductive / non-parameterless structure / external): text identity only, not a proof')
            else: recs[full]=dict(status='NO_FRESH_EMISSION',reason='no overflow-checks-on fresh emission (PCQC_COVERAGE / PCQ_E037-E040) declares this name (or a recorded prefix variant); extraction failures are in PCQC_FAILURES.json')
    for full,e in recs.items():
        e['superseded_earlier_status']=old_info(m,full)
        o=e['superseded_earlier_status']
        if o['status'].startswith('PROVED') and not e['status'].startswith('PROVED'):
            e['earlier_proof_note']='the earlier proof was against '+str(o['fresh'])+(' (overflow-checks-on)' if o['fresh_overflow_on'] else ' (not overflow-checks-on: does not count under the 2026-11-09 ruling)')
    # classification: checked vs wrapping that persists with overflow-on emission
    for full,e in recs.items():
        ops=e.pop('_ops',None)
        if e['status']=='FAILED' and ops:
            ov=[o for o in ops if any(OV.search(t) for side in o for t in side)]
            if ov: e['status']='CONFIG_MISMATCH';e['config_mismatch_reason']='fresh (overflow-checks-on) and gate bodies still differ in a checked/wrapping/overflowing/saturating operation';e['overflow_op_diff']=[[' '.join(s) for s in o] for o in ov][:6]
    changed=True
    while changed:
        changed=False
        for full,e in recs.items():
            if e['status']=='FAILED' and 'blocked by failed callee' in (e.get('error') or ''):
                names=[b.strip() for b in e['error'].split(':',1)[1].split(',')]
                if any(any(k.endswith('.'+b) and recs[k]['status']=='CONFIG_MISMATCH' for k in recs) for b in names):
                    e['status']='CONFIG_MISMATCH';e['config_mismatch_reason']='blocked by a callee equality that is CONFIG_MISMATCH: '+','.join(names);changed=True
    for full,e in recs.items():
        tot[e['status']]=tot.get(e['status'],0)+1
        if not e['status'].startswith('PROVED'): p3.append(dict(module=m,definition=full,**{k:v for k,v in e.items() if k not in('superseded_earlier_status',)},earlier=e['superseded_earlier_status']))
    out[m]=dict(plan_status=pl['status'],gate_namespace=gns,passes=[dict(label=label(m,ps),kind=ps['kind'],run=ps['run'],fresh_dir=ps['fresh_dir'],name_map=ps.get('name_map')) for ps in pl['passes']],reached=recs)
def G_ren(x): return x
Path(H/'PCUE_EQ_STATUS.json').write_text(json.dumps(dict(schema='PCUE_EQ_STATUS/1',target_established=False,
 supersedes='PCUA_EQ_STATUS.json and PCUD_EQ_STATUS.json for every definition listed here (each record carries superseded_earlier_status). Only overflow-checks-on fresh emissions count; a definition with no overflow-checks-on emission is NO_FRESH_EMISSION even if P2a/P2d recorded a proof against an overflow-off emission.',
 totals=tot,verify_bundles=AX,modules=out),indent=1))
Path(H/'PCUE_FOR_P3.json').write_text(json.dumps(dict(schema='PCUE_FOR_P3/1',target_established=False,note='Every non-PROVED definition with its earlier P2a/P2d status. CONFIG_MISMATCH: a checked-vs-wrapping difference persisting with an overflow-checks-on emission, both bodies recorded. NO_FRESH_EMISSION: waits for an overflow-checks-on emission (P1c failures: Aeneas tool limits).',items=p3),indent=1))
print(tot)
