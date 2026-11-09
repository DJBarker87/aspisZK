#!/usr/bin/env python3
"""PCUF_final.py: PCUF_EQ_STATUS.json and PCUF_FOR_P3.json from the final generator states and the verification receipts.
One record per reached definition of every P2f module (the reached sets are those of the P2r/P2b/P2c status files)."""
import json,re,sys,difflib
from pathlib import Path
sys.dont_write_bytecode=True
import PCUF_gen_equalities as G
H=Path(__file__).resolve().parent;EV=H.parent
PLAN=json.load(open(H/'PCUF_PLAN.json'));ORIG=json.load(open(H/'module_origin.json'));REACHED=json.load(open(H/'module_reached.json'))
SUP={"PCQC_E002","PCQC_E003","PCQC_E004","PCQC_E011","PCQ_E039","PCQ_E040"}
OK_AX={'propext','Classical.choice','Quot.sound'}
OV=re.compile(r'wrapping_|checked_|overflowing_|saturating_')
def label(m,ps): return m.replace('.','_')+ps['tag']
bundles=json.load(open(H/'gen/bundles.json'));VER=json.load(open(H/'gen/verify_attempts.json'))
lab2v={}
for bk,att in VER.items():
    for l in bundles[bk]: lab2v[l]=(bk,att)
AX={}
for bk,att in VER.items():
    r=json.load(open(H/att/'receipt.json'))
    AX[bk]=dict(attempt=att,target=r['module'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r.get('source_revision'),source_tree_dirty=r.get('source_tree_dirty'),axioms=' '.join(' '.join(r['print_axioms']).split()))
EARLIER={}
for f,tool in [("prov-p2r-20261109/PCUE_EQ_STATUS.json","P2r"),("prov-p2b-20261109/PCUB_EQ_STATUS.json","P2b"),("prov-p2c-20261109/PCUC_EQ_STATUS.json","P2c")]:
    for m,v in json.load(open(EV/f))["modules"].items():
        for n,r in v["reached"].items(): EARLIER[(m,n)]=dict(tool=tool,status=r["status"],uses_superseded=sorted(x for x in SUP if x+"_emitted" in json.dumps(r) or ('"fresh_run": "%s"'%x) in json.dumps(r)),record=r)
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
def gate_cfg(path):
    t=Path(EV/path).read_text() if path else ''
    chk=len(re.findall(r'←\s*[\w.()]+\s+[-+*]\s+[\w.()]+',t));wr=len(re.findall(r'wrapping_|Wrapping',t))
    return 'OFF' if wr and not chk else 'ON'
out={};p3=[];tot={}
for m,pl in PLAN.items():
    gns=None
    reached=REACHED[m]
    recs={full:None for full in reached}
    for ps in pl['passes']:
        lab=label(m,ps);st,rnd=latest_state(lab)
        if st is None: continue
        gns=gns or None
        g=EV/ps['gate'];gt=g.read_text()
        if ps.get('gate_namespace'): gt,_=G.extract_namespace(gt,ps['gate_namespace']); pgns=ps['gate_namespace']
        else: pgns=re.findall(r'(?m)^namespace\s+(\S+)',G.uncomment(gt))[0]
        gb={b['name']:b for b in G.parse_blocks(gt) if b['kind']=='decl'}
        for xg in ps.get('gate_extra') or []:
            for b in G.parse_blocks((EV/xg).read_text()):
                if b['kind']=='decl' and b['name'] not in gb: gb[b['name']]=b
        k='Types.lean' if ps['kind']=='Types' else 'Funs.lean'
        ftxt=(EV/ps['fresh_dir']/k).read_text()
        for rn in ps.get('rename_fresh') or []:
            o,nw=rn.split('=',1);ftxt=re.sub(r'(?<![\w.])'+re.escape(o)+(r'(?=[\w.])' if o.endswith('.') else r'(?![\w.])'),nw,ftxt)
        fb={b['name']:b for b in G.parse_blocks(ftxt) if b['kind']=='decl'}
        nm=ps.get('name_map',{});vk=lab2v.get(lab)
        cfg=gate_cfg(ps['gate'])
        for n,x in st['defs'].items():
            gn=nm.get(n,n);full=pgns+'.'+gn
            if full not in recs: continue
            thm=f"PRVEq.{m}{ps['tag']}.{n}"
            base=dict(pass_label=lab,theorem=thm,theorem_file=f"PRVEq_{lab}.lean",fresh_source=ps['fresh_dir'],fresh_run=ps['run'],aeneas_tool=ps['tool'],configuration='ON',gate_configuration_by_text=cfg,fresh_overflow_checks_on=True,fresh_name=n,
                      gate_source=ps['gate'],statement=f"@{pgns}.PRVFresh_{lab}.{n} = @{pgns}.{gn}",verify_bundle=vk[0] if vk else None,verify_attempt=vk[1] if vk else None,state_round=rnd)
            if x['status']=='proved':
                isstruct=fb.get(n,{}).get('dkind')=='structure'
                stt='PROVED_EQUIV' if isstruct else ('PROVED_RFL' if x['stage']==1 else 'PROVED_UNFOLD')
                ent=dict(base,status=stt)
                a=AX.get(vk[0],{}).get('axioms','') if vk else ''
                mm=re.search(r"'"+re.escape(thm)+r"(?:\.equiv)?' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",a)
                if mm:
                    axs=set(z.strip() for z in (mm.group(2) or '').split(',') if z.strip());ent['axioms']=sorted(axs);ent['axioms_ok']=axs<=OK_AX
                else: ent['axioms']='NOT_FOUND_IN_VERIFY_RECEIPT';ent['axioms_ok']=None
            else:
                ent=dict(base,status='FAILED',failure_class=x.get('class'),error=(x.get('error') or '')[:400],callees=x.get('callees'))
                if n in fb and gn in gb:
                    ent['diff_normalized']=udiff(fb[n],gb[gn]);ent['_ops']=opdiff(fb[n],gb[gn])
                    ent['fresh_body']=G.norm_decl(fb[n])[:2500];ent['gate_body']=G.norm_decl(gb[gn])[:2500]
            cur=recs[full]
            if cur is None or (ent['status'].startswith('PROVED') and not cur['status'].startswith('PROVED')): recs[full]=ent
    for full in list(recs):
        e0=EARLIER[(m,full)]
        if recs[full] is None:
            r=dict(e0['record']);r['status']=e0['status'];r['carried_from']=e0['tool']+' (no P2f pass covered this definition)'
            if pl['status']=='NO_ELIGIBLE_EMISSION': r['carried_note']='no eligible fresh emission in PCUF_EMISSION_INDEX.json for this module'
            if e0['status']=='GATE_SOURCE_UNAVAILABLE':
                r['status']='NO_FRESH_EMISSION';r['reason']='gate source now accepted (PCUF change 5, multi-namespace gate support); no eligible fresh emission declares this name in the selected namespace'
                r['carried_from']='P2r GATE_SOURCE_UNAVAILABLE reclassified by P2f'
            if e0['status'].startswith('PROVED') and e0['uses_superseded']:
                r['status']='PROVED_AGAINST_SUPERSEDED_EMISSION_NOT_REPROVED';r['superseded_emissions']=e0['uses_superseded']
            recs[full]=r
    for full,e in recs.items():
        e0=EARLIER[(m,full)]
        e['supersedes']=dict(tool=e0['tool'],status=e0['status'],superseded_emissions_used=e0['uses_superseded'])
        ops=e.pop('_ops',None)
        if e['status']=='FAILED' and ops:
            ov=[o for o in ops if any(OV.search(t) for side in o for t in side)]
            if ov: e['status']='CONFIG_MISMATCH';e['config_mismatch_reason']='fresh (overflow-checks-on) and gate bodies still differ in a checked/wrapping/overflowing/saturating operation';e['overflow_op_diff']=[[' '.join(s) for s in o] for o in ov][:6]
        # a new FAILED never overrides an earlier proof against a non-superseded eligible emission
        if e['status'] in('FAILED','CONFIG_MISMATCH') and e0['status'].startswith('PROVED') and not e0['uses_superseded']:
            e['later_failed_attempt']=dict(status=e['status'],error=e.get('error'),fresh_run=e.get('fresh_run'))
            keep=dict(e0['record']);keep['status']=e0['status'];keep['carried_from']=e0['tool']+' (earlier proof against a non-superseded eligible emission stands)'
            keep['supersedes']=e['supersedes'];keep['later_failed_attempt']=e['later_failed_attempt'];recs[full]=keep
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
        if not e['status'].startswith('PROVED'): p3.append(dict(module=m,definition=full,**{k:v for k,v in e.items() if k not in('superseded_earlier_status','record')}))
    out[m]=dict(origin=pl['origin'],plan_status=pl['status'],passes=[dict(label=label(m,ps),kind=ps['kind'],run=ps['run'],tool=ps['tool'],fresh_dir=ps['fresh_dir'],name_map=ps.get('name_map'),rename_fresh=ps.get('rename_fresh'),gate_namespace=ps.get('gate_namespace'),gate_extra=ps.get('gate_extra')) for ps in pl['passes']],reached=recs)
Path(H/'PCUF_EQ_STATUS.json').write_text(json.dumps(dict(schema='PCUF_EQ_STATUS/1',target_established=False,
 supersedes='PCUE_EQ_STATUS.json, PCUB_EQ_STATUS.json and PCUC_EQ_STATUS.json for the definitions of the 59 modules listed here (each record carries `supersedes`). Only eligible emissions count: overflow-checks ON, exit 0, not superseded by PCQF_SUPERSEDES.json.',
 totals=tot,verify_bundles=AX,modules=out),indent=1))
Path(H/'PCUF_FOR_P3.json').write_text(json.dumps(dict(schema='PCUF_FOR_P3/1',target_established=False,note='Every non-PROVED definition of the P2f modules with its earlier status. Heartbeat timeouts (200000, never raised) and WideToBytes-class items stay P3.',items=p3),indent=1))
print(tot)
