#!/usr/bin/env python3
"""PCUC_final.py: per module / per reached definition status from the state2 files, with diffs and goals.
Writes PCUC_EQ_STATUS.json, PCUC_FOR_P3.json. Statuses: PROVED_RFL, PROVED_UNFOLD, FAILED(class), CONFIG_PENDING_OVERFLOW_CHECKS,
TEXT_IDENTICAL_ONLY, NO_FRESH_EMISSION, NO_COMMON_LEAN_NAME."""
import json,re,sys,difflib
from pathlib import Path
sys.dont_write_bytecode=True
import PCUC_gen_equalities as G
prep=json.load(open('gen_prepared.json'));P=json.load(open('PCUC_PARTITION.json'))['modules']
COV=json.load(open('../prov-p1c-20261109/PCQC_COVERAGE.json'))
MISSMAP={}
for sp,v in COV['specs'].items():
    for dn,d in v['definitions'].items():
        if d['status']!='FRESH_PRESENT': MISSMAP.setdefault(dn,[]).append((sp,d['status'],[a['run']+':exit'+str(a['exit']) for a in v['attempts']]))
VER=json.load(open('gen/verify_attempts.json'));ROOTS=json.load(open('gen/roots.json'))
OV=re.compile(r'wrapping_|checked_|overflowing_|saturating_')
def label(m,ps): return m.replace('.','_')+ps['tag']
def blocks(path):
    return {b['name']:b for b in G.parse_blocks(Path(path).read_text()) if b['kind']=='decl'}
def toks(b): return G.norm_decl(b).split()
def diff(fb,gb,limit=1800):
    a,b=toks(fb),toks(gb)
    d=[l for l in difflib.unified_diff(a,b,'fresh','gate',n=2,lineterm='') ]
    s=' '.join(d[2:])
    return s[:limit]
def opdiff(fb,gb):
    a,b=toks(fb),toks(gb)
    sm=difflib.SequenceMatcher(a=a,b=b,autojunk=False)
    ch=[(a[i1:i2],b[j1:j2]) for t,i1,i2,j1,j2 in sm.get_opcodes() if t!='equal']
    return ch
def goal_from_logs(lab,n,logs):
    return None
# axioms per verify attempt
AX={}
for bk,att in VER.items():
    r=json.load(open(f'{att}/receipt.json'))
    AX[bk]=dict(att=att,exit=r['exit_status'],wall=r['wall_seconds'],rss=r['peak_rss_kib'],swaps=r['swaps'],axioms=' '.join(' '.join(r['print_axioms']).split()))
lab2b={l:k for k,v in json.load(open('gen/bundles.json')).items() for l in v}
OK_AX={'propext','Classical.choice','Quot.sound'}
out={};p3=[];tot={}
MODS=['AspisR1TerminalDecoder.Types','AspisR1TerminalDecoder.Funs','NFY_Part042','NFY_Part043','Port23PUSH_Source','AspisR1PublicPreparation.Types','AspisR1PublicPreparation.Funs','AspisR1AdapterReconstruct.Types','AspisR1AdapterReconstruct.Funs']
for m in MODS:
    rviews=[v for k,v in prep.items() if v['module']==m];r=dict(rviews[0]);r['passes']=[dict(ps,_view=v['view'],_kind=v['kind']) for v in rviews for ps in v['passes']];mod=P[m];reached=list(mod['reached_definitions']);rs={}
    for ps in r['passes']:
        lab=label(m,ps)
        st=json.load(open(f'gen/PRVEq_{lab}.state2.json'));rep=json.load(open(f'gen/PRVEq_{lab}.report2.json'))
        gns=rep['gate_namespace']
        fresh_path=Path('inputs/fresh_'+lab)/('Types.lean' if ps['_view']=='Types' else 'Funs.lean')
        fb=blocks(fresh_path);gb=blocks('inputs/gate_'+lab+'.lean')
        for n,x in st['defs'].items():
            full=gns+'.'+n
            if full not in mod['reached_definitions']: continue
            cur=rs.get(full)
            thm=f"PRVEq.{m}{ps['tag']}.{n}"
            if x['status']=='proved':
                ent=dict(status='PROVED_RFL' if x['stage']==1 else 'PROVED_UNFOLD',pass_tag=ps['tag'],theorem=thm,verify_attempt=VER.get(lab2b.get(lab)),fresh_source=ps['fresh_dir'],gate_source=ps['gate_path'])
                ax=AX.get(lab2b.get(lab),{}).get('axioms','')
                mm=re.search(r"'"+re.escape(thm)+r"(?:\.equiv)?' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",ax)
                if mm:
                    axs=set(a.strip() for a in (mm.group(2) or '').split(',') if a.strip())
                    ent['axioms']=sorted(axs);ent['axioms_ok']=axs<=OK_AX
                else: ent['axioms']='NOT_FOUND_IN_VERIFY_RECEIPT';ent['axioms_ok']=None
                if cur is None or cur['status'].startswith(('FAILED','CONFIG','NO_','TEXT')): rs[full]=ent
            else:
                ent=dict(status='FAILED',pass_tag=ps['tag'],failure_class=x.get('class'),error=(x.get('error') or '')[:400],statement=f"@PRVFresh_{lab}.{n} = @{gns}.{n}",
                         fresh_source=ps['fresh_dir'],gate_source=ps['gate_path'],callees=x.get('callees'))
                # root causes: fresh declarations in the transitive callee closure (within this state) that failed to elaborate in the round-1 probe
                RT=ROOTS.get(lab,{});seen=set();stack=[n];rc={}
                while stack:
                    c=stack.pop()
                    if c in seen: continue
                    seen.add(c)
                    if c in RT: rc[c]=RT[c]
                    stack+=[q for q in (st['defs'].get(c,{}).get('callees') or []) if q in st['defs']]
                ent['root_causes']=rc if rc else 'none recorded in the round-1 probe roots (goal-level failure: see statement and diff_normalized)'
                if n in fb and n in gb:
                    ent['diff_normalized']=diff(fb[n],gb[n]);ent['_ops']=opdiff(fb[n],gb[n])
                    ent['body_identical']=toks(fb[n])==toks(gb[n])
                if cur is None or cur['status'] in('NO_COMMON_LEAN_NAME','TEXT_IDENTICAL_ONLY'): rs[full]=ent
    cov={c for ps in r['passes'] for c in ps['covers']}
    for n in reached:
        if n in rs: continue
        if n in cov:
            tx=None
            for ps in r['passes']:
                if n not in ps['covers']: continue
                lab=label(m,ps);gns=json.load(open(f'gen/PRVEq_{lab}.report2.json'))['gate_namespace']
                ln=n[len(gns)+1:] if n.startswith(gns+'.') else n
                fp=Path('inputs/fresh_'+lab)/('Types.lean' if ps['_view']=='Types' else 'Funs.lean');fb2=blocks(fp);gb2=blocks('inputs/gate_'+lab+'.lean')
                if ln in fb2 and ln in gb2:
                    same=toks(fb2[ln])==toks(gb2[ln])
                    tx=dict(status='TEXT_IDENTICAL_ONLY' if same else 'TEXT_DIFFERS',pass_tag=ps['tag'],fresh_source=ps['fresh_dir'],gate_source=ps['gate_path'],
                            reason='both declarations exist under the same Lean name; the generator emits no Lean statement for this declaration shape (inductive, or structure outside the simple-structure fragment, or a def reachable only as a type abbreviation); '+('normalized text identical: NOT a Lean-proved equality' if same else 'normalized text differs'),
                            **({} if same else dict(diff_normalized=diff(fb2[ln],gb2[ln]))))
                    break
            if tx: rs[n]=tx; continue
            rs[n]=dict(status='NO_COMMON_LEAN_NAME',reason='partition covers this definition by Rust symbol in the fresh emission, but no declaration of the same Lean name exists in both fresh and gate (name or crate-prefix difference, or a non-comparable declaration shape); no Lean statement generated',
                       fresh_sources=[ps['fresh_dir'] for ps in r['passes'] if n in ps['covers']])
        else:
            rs[n]=dict(status='NO_FRESH_EMISSION',reason='no overflow-checks-on fresh emission contains a same-symbol declaration (partition coverage as recorded); P1 reference in p1_reference',p1_reference=(MISSMAP.get(n) or 'no P1 selection attempted this definition in PCQC_COVERAGE specs (cut-crate or unselected); see PCQ/PCQC failure lists'),partition_coverage=mod['reached_definitions'][n].get('coverage'))
    out[m]=dict(group=mod['group'],subgroup=mod['subgroup'],kind=r['kind'],passes=r['passes'],reached=rs)
# overflow-check classification (lead instruction): checked-vs-wrapping diffs are CONFIG_PENDING, never SEMANTIC
for m,v in out.items():
    rs=v['reached']
    for full,e in rs.items():
        if e['status']=='FAILED' and e.get('_ops'):
            ov=[o for o in e['_ops'] if any(OV.search(t) for side in o for t in side)]
            if ov and not e.get('body_identical'):
                e['status']='CONFIG_MISMATCH';e['config_mismatch_reason']='fresh (overflow-checks on) and gate bodies still differ in a checked/wrapping/overflowing/saturating operation; both normalized bodies in fresh_body/gate_body; reported to the lead'
                e['overflow_op_diff']=[[' '.join(s) for s in o] for o in ov][:6]
    changed=True
    while changed:
        changed=False
        for full,e in rs.items():
            if e['status']=='FAILED' and 'blocked by failed callee' in (e.get('error') or ''):
                bl=(e['error'].split(':',1)[1]).strip().split(',')
                gns=full.rsplit('.',0)[0]
                names=[b for b in bl]
                hit=any(any(k.endswith('.'+b) and rs[k]['status']=='CONFIG_MISMATCH' for k in rs) for b in names)
                if hit:
                    e['status']='CONFIG_MISMATCH';e['config_mismatch_reason']='blocked by a callee equality that is CONFIG_MISMATCH: '+','.join(names);changed=True
    for full,e in rs.items():
        e.pop('_ops',None)
        tot[e['status']]=tot.get(e['status'],0)+1
        if e['status']!='PROVED_RFL' and e['status']!='PROVED_UNFOLD':
            p3.append(dict(module=m,definition=full,**{k:v for k,v in e.items() if k not in ('fresh_sources',)}))
Path('PCUC_EQ_STATUS.json').write_text(json.dumps(dict(target_established=False,totals=tot,verify_bundles=AX,modules=out),indent=1))
Path('PCUC_FOR_P3.json').write_text(json.dumps(dict(target_established=False,note='CONFIG_MISMATCH entries (overflow-on fresh vs gate still differ in checked/wrapping form) go to the lead; FAILED entries are data for P3; NO_FRESH_EMISSION waits for P1a/P1 failure lists.',items=p3),indent=1))
print(tot)
