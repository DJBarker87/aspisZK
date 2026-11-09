#!/usr/bin/env python3
"""PCUD_final.py: per module / per reached definition status from the state2 files, with diffs and goals.
Writes PCUD_EQ_STATUS.json, PCUD_FOR_P3.json. Statuses: PROVED_RFL, PROVED_UNFOLD, FAILED(class), CONFIG_PENDING_OVERFLOW_CHECKS,
TEXT_IDENTICAL_ONLY, NO_FRESH_EMISSION, NO_COMMON_LEAN_NAME."""
import json,re,sys,difflib
from pathlib import Path
sys.dont_write_bytecode=True
import PCUD_gen_equalities as G
prep=json.load(open('gen_prepared.json'));P=json.load(open('PCUD_PARTITION.json'))['modules']
VER=json.load(open('gen/verify_attempts.json'))
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
for m in json.load(open('PCUD_modules.json')):
    r=prep[m];mod=P[m];reached=list(mod['reached_definitions']);rs={}
    for ps in r['passes']:
        lab=label(m,ps)
        st=json.load(open(f'gen/PRVEq_{lab}.state2.json'));rep=json.load(open(f'gen/PRVEq_{lab}.report2.json'))
        gns=rep['gate_namespace']
        fresh_path=Path('inputs/fresh_'+lab)/('Types.lean' if r['kind']=='Types' else 'Funs.lean')
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
                if n in fb and n in gb:
                    ent['diff_normalized']=diff(fb[n],gb[n]);ent['_ops']=opdiff(fb[n],gb[n])
                    ent['body_identical']=toks(fb[n])==toks(gb[n])
                if cur is None or cur['status'] in('NO_COMMON_LEAN_NAME','TEXT_IDENTICAL_ONLY'): rs[full]=ent
    cov={c for ps in r['passes'] for c in ps['covers']}
    for n in reached:
        if n in rs: continue
        if n in cov:
            rs[n]=dict(status='NO_COMMON_LEAN_NAME',reason='partition covers this definition by Rust symbol in the fresh emission, but no declaration of the same Lean name exists in both fresh and gate (name or crate-prefix difference, or a non-comparable declaration shape); no Lean statement generated',
                       fresh_sources=[ps['fresh_dir'] for ps in r['passes'] if n in ps['covers']])
        else:
            rs[n]=dict(status='NO_FRESH_EMISSION',reason='no frozen fresh emission contains a same-symbol declaration (partition UNCOVERED); P1 failure/pending reference: PCQ_B_FAILURES.json / P1a pending',partition_coverage=mod['reached_definitions'][n].get('coverage'))
    out[m]=dict(group=mod['group'],subgroup=mod['subgroup'],kind=r['kind'],passes=r['passes'],reached=rs)
# overflow-check classification (lead instruction): checked-vs-wrapping diffs are CONFIG_PENDING, never SEMANTIC
for m,v in out.items():
    rs=v['reached']
    for full,e in rs.items():
        if e['status']=='FAILED' and e.get('_ops'):
            ov=[o for o in e['_ops'] if any(OV.search(t) for side in o for t in side)]
            if ov and not e.get('body_identical'):
                e['status']='CONFIG_PENDING_OVERFLOW_CHECKS';e['config_pending_reason']='fresh/gate bodies differ in a checked/wrapping/overflowing/saturating operation (extraction-configuration artefact suspected, lead message: historical extractions used overflow-checks=yes); not classified SEMANTIC'
                e['overflow_op_diff']=[[' '.join(s) for s in o] for o in ov][:6]
    changed=True
    while changed:
        changed=False
        for full,e in rs.items():
            if e['status']=='FAILED' and 'blocked by failed callee' in (e.get('error') or ''):
                bl=(e['error'].split(':',1)[1]).strip().split(',')
                gns=full.rsplit('.',0)[0]
                names=[b for b in bl]
                hit=any(any(k.endswith('.'+b) and rs[k]['status']=='CONFIG_PENDING_OVERFLOW_CHECKS' for k in rs) for b in names)
                if hit:
                    e['status']='CONFIG_PENDING_OVERFLOW_CHECKS';e['config_pending_reason']='blocked by a callee equality that is CONFIG_PENDING_OVERFLOW_CHECKS: '+','.join(names);changed=True
    for full,e in rs.items():
        e.pop('_ops',None)
        tot[e['status']]=tot.get(e['status'],0)+1
        if e['status']!='PROVED_RFL' and e['status']!='PROVED_UNFOLD':
            p3.append(dict(module=m,definition=full,**{k:v for k,v in e.items() if k not in ('fresh_sources',)}))
Path('PCUD_EQ_STATUS.json').write_text(json.dumps(dict(target_established=False,totals=tot,verify_bundles=AX,modules=out),indent=1))
Path('PCUD_FOR_P3.json').write_text(json.dumps(dict(target_established=False,note='CONFIG_PENDING_OVERFLOW_CHECKS entries await the lead (no SEMANTIC classification of checked-vs-wrapping differences); FAILED entries are data for P3; NO_FRESH_EMISSION waits for P1a/P1 failure lists.',items=p3),indent=1))
print(tot)
