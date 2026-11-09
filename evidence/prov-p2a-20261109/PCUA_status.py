#!/usr/bin/env python3
"""PCUA_status.py: build per-job definition status (PROVED_RFL / PROVED_UNFOLD / FAILED(...)) from the generator reports, the probe
logs and the final verification receipts. Output: PCUA_JOB_STATUS.json (one entry per (gate module, fresh emission) job)."""
import sys,json,re
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H))
import PCUA_gen_equalities as G, PCUA_jobs as J, PCUA_diff as D
PROBE={'DotDecode':('A1','probe_A1.log','L006'),'NativeDots':('B1','probe_B1.log','L006'),'NativeTypesQ415':('C1','probe_C1.log','L006'),'Stage2Q415':('C1','probe_C1.log','L006'),
 'NativeFunsQ415':('D1','probe_D1.log','L006'),'CWTypes':('F1','probe_F1.log','L006'),'S1M31':('F1','probe_F1.log','L006'),'CWFuns':('F1','probe_F1.log','L006'),
 'NativeFunsE410':('H1','probe_H1.log','L009'),'NativeTypesE416':('H1','probe_H1.log','L009'),'Stage2E003':('H1','probe_H1.log','L009'),
 'NativeTypesE003':('H2','probe_H2.log','L010'),'Stage2E010':('H2','probe_H2.log','L010'),'CtlCWFuns':('K1','probe_K1.log',None)}
SCOPE={'L006':('G1','PCUA_L006'),'L009':('H1v','PCUA_L009'),'L010':('H2v','PCUA_L010')}
def msgs(log,offs,key):
    inv={b:a for a,b in json.loads(Path(offs).read_text())[key]['line_map']};out={};cur=None
    for l in Path(log).read_text().splitlines():
        m=re.match(r'^\S*?PRVEq_bundle_\w+\.lean:(\d+):(\d+): (error|warning|info)\b[^:]*:?\s*(.*)$',l)
        if m:
            cur=None
            if m.group(3)=='error' and int(m.group(1)) in inv:
                cur=[inv[int(m.group(1))],m.group(4)];out.setdefault(cur[0],[]).append(cur)
        elif cur is not None and not l.startswith('PRV-S') and len(cur[1])<700: cur[1]+='\n'+l
    return out
def job_status(jid):
    j=J.JOBS[jid];stem='PRVEq_'+jid;rep=json.loads((H/(stem+'.report.json')).read_text());st1=json.loads((H/(stem+'.state1.json')).read_text())
    b,log,scope=PROBE[jid];m=msgs(H/log,H/('PRVEq_bundle_'+b+'.offsets.json'),'PRVEq_'+j['M'].replace('.','_'))
    kind=j.get('kind') or ('types' if j['M'].endswith('Types') else 'funs')
    fresh_text=(Path(j['fresh'])/('Types.lean' if kind=='types' else 'Funs.lean')).read_text()
    fb=[x for x in G.parse_blocks(fresh_text) if x['kind']=='decl'];fnames=[x['name'] for x in fb];body={x['name']:x['body'] for x in fb}
    def closure(n):
        seen=[];todo=[n]
        while todo:
            c=todo.pop(0)
            if c in seen:continue
            seen.append(c);todo+=G.callees(body.get(c,''),fnames,c)
        return seen
    def fresh_err(n):
        for c in closure(n):
            r=st1['fresh_lines'].get(c)
            if r:
                for ln in range(r[0],r[1]+1):
                    if ln in m:return c,m[ln][0][1][:500]
        return None,None
    ext=set(rep.get('external_funs') or [])|set(rep.get('external_types') or [])
    def reach_ext(n):
        toks=set();
        for c in closure(n):toks|=set(G.lean_ident_tokens(body.get(c,'')))
        return sorted(toks&ext)
    diffs=D.diff_job(jid) if jid!='CtlCWFuns' else {}
    out=[]
    for n,d in rep['per_definition'].items():
        e=dict(definition=n,reached=d['reached'],callees=d['callees'],body_text_identical=d['body_identical'],mentions_differing_types=d.get('mentions_differing_types',[]))
        e['reaches_external_boundaries']=reach_ext(n)
        if d['status']=='proved':
            e['status']='PROVED_RFL' if d['stage']==1 else 'PROVED_UNFOLD' if d['stage']==2 else 'PROVED_EQUIV' if d['stage'] else 'PROVED'
            if d['dkind']=='structure-equiv':e['status']='PROVED_EQUIV'
        else:
            e['status']='FAILED';e['error_class']=[]
            err=d.get('error','');e['reason']=err[:300]
            if d.get('fresh_dropped'):
                c,t=fresh_err(n);e['first_failing_fresh_declaration']=c;e['first_failing_goal_or_error']=t;e['error_class'].append('FRESH_DECLARATION_DOES_NOT_ELABORATE_AGAINST_GATE')
            elif err.startswith('blocked by'):
                e['error_class'].append('BLOCKED_BY_FAILED_CALLEE');e['blocked_by']=d.get('blocked_by')
            else:
                dl=st1['defs'].get(n,{}).get('lines')
                g=None
                if dl:
                    for ln in range(dl[0],dl[1]+1):
                        if ln in m:g=m[ln][0][1][:900];break
                e['first_failing_goal_or_error']=g
                e['error_class'].append('UNSOLVED_GOAL_AFTER_UNFOLD' if g and 'unsolved' in g else 'ERROR')
            df=diffs.get(n)
            if df:
                e['normalized_text_diff_gate_to_fresh']=df['diff_gate_to_fresh'];
                if 'wrapping_' in df['diff_gate_to_fresh'] :e['error_class'].append('CHECKED_VS_WRAPPING_ARITHMETIC')
        out.append(e)
    return dict(job=jid,gate_module=j['M'],kind=kind,fresh_dir=str(Path(j['fresh']).relative_to(H.parent)) if str(j['fresh']).startswith(str(H.parent)) else j['fresh'],
        fresh_namespace=j['ns'],generated_file='PRVEq_'+jid+'.lean',probe_scope=PROBE[jid][1],final_scope=scope,types_identity=rep.get('types_identity'),
        external_funs=rep.get('external_funs'),external_types=rep.get('external_types'),names_resolved_to_gate_funs=rep.get('names_resolved_to_gate_funs'),
        fresh_dropped=rep.get('fresh_dropped'),counts=rep['counts'],definitions=out)
if __name__=='__main__':
    res={jid:job_status(jid) for jid in PROBE}
    (H/'PCUA_JOB_STATUS.json').write_text(json.dumps(dict(schema='PCUA_JOB_STATUS/1',target_established=False,jobs=res),indent=1))
    for jid,r in res.items():print(jid,r['gate_module'],{k:sum(1 for d in r['definitions'] if d['status']==k) for k in sorted({d['status'] for d in r['definitions']})})
