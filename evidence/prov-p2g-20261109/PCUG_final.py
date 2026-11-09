#!/usr/bin/env python3
"""PCUG_final.py: PCUG_EQ_STATUS.json, PCUG_FOR_P3.json, PCUG_ALL_STATUS.json, PCUG_NONFROZEN_CANDIDATES.json from the final generator states, the verification receipts
and PCUF_ALL_STATUS.json. One record per scope definition (PCUG_PLAN.json passes[*].scope) ; the other definitions of PCUF_ALL_STATUS are carried unchanged.
Per-definition required configuration (PCUG-3): the gate declaration text of the definition contains `wrapping_` -> OFF (wrapping on plain operators), else ON.
Superseding rule (recorded in the output): a new record replaces the PCUF record when it is a PROVED record with a correct basis, or a non-proved record with a correct basis,
or when the old record is itself not a proved record with a correct basis; the old status stays in `supersedes`."""
import json,re,sys,difflib,copy
from pathlib import Path
sys.dont_write_bytecode=True
import PCUG_gen_equalities as G
H=Path(__file__).resolve().parent;EV=H.parent
PLAN=json.load(open(H/'PCUG_PLAN.json'));BUND=json.load(open(H/'gen/bundles.json'))
OLD=json.load(open(EV/'prov-p2f-20261109/PCUF_ALL_STATUS.json'))
OK_AX={'propext','Classical.choice','Quot.sound'}
OV=re.compile(r'wrapping_|checked_|overflowing_|saturating_')
VER={'V1':'PCUG_L021','V2':'PCUG_L022'}
RETIRED={'RPu_FIq_Native14_p2':dict(attempts=['PCUG_L017','PCUG_L019','PCUG_L020'],reason='the fresh declarations of the PCQG_E015 pass (closure of terminal_parts/composition_parts/equality_value, 280 gate / 267 fresh declarations) do not finish elaborating within the 180 s Lean scope: PCUG_L017 (Native14 single 14-definition pass, 119 theorems), PCUG_L019 (this pass, 77 theorems) and PCUG_L020 (diagnostic: fresh declarations only, no theorem) all exit 124 with empty output; shape retired after three failures, not rerun, no cap or timeout raised')}
def label(m,ps): return m.replace('.','_')+ps['tag']
def label_of_bundle():
    d={}
    for bk,att in VER.items():
        for l in BUND[bk]: d[l]=(bk,att)
    return d
LAB2V=label_of_bundle()
AX={}
for bk,att in VER.items():
    r=json.load(open(H/att/'receipt.json'))
    AX[bk]=dict(attempt=att,target=r['module'],exit=r['exit_status'],wall_seconds=r['wall_seconds'],peak_rss_kib=r['peak_rss_kib'],swaps=r['swaps'],source_revision=r.get('source_revision'),source_tree_dirty=r.get('source_tree_dirty'),axioms=' '.join(' '.join(r['print_axioms']).split()))
def latest(lab,pref):
    for k in (3,2,1):
        p=H/f'gen/PRVEq_{lab}.{pref}{k}.json'
        if p.exists(): return json.load(open(p)),k
    return None,0
def toks(b): return G.norm_decl(b).split()
def opdiff(fb,gb):
    a,b=toks(fb),toks(gb);sm=difflib.SequenceMatcher(a=a,b=b,autojunk=False)
    return [(a[i1:i2],b[j1:j2]) for t,i1,i2,j1,j2 in sm.get_opcodes() if t!='equal']
def udiff(fb,gb,limit=1800):
    d=list(difflib.unified_diff(toks(fb),toks(gb),'fresh','gate',n=2,lineterm=''));return ' '.join(d[2:])[:limit]
def apply_rename(t,rns):
    for rn in rns or []:
        o,nw=rn.split('=',1);t=re.sub(r'(?<![\w.])'+re.escape(o)+(r'(?=[\w.])' if o.endswith('.') else r'(?![\w.])'),nw,t)
    return t
def fresh_closure(fn,fb,names_gate,axioms,ext):
    """closure over fresh declarations; returns (fresh names, gate-resolved names, fresh axioms)"""
    seen=set();stack=[fn];res=set();axs=set()
    fnames=set(fb)
    while stack:
        n=stack.pop()
        if n in seen: continue
        seen.add(n)
        if fb[n]['dkind'] in ('axiom','opaque'): axs.add(n)
        for t in set(G.lean_ident_tokens(fb[n]['body'])):
            if t in fnames and t not in seen: stack.append(t)
            elif t in names_gate and t not in fnames: res.add(t)
    return seen,res,axs
def diff_class(e):
    err=e.get('error') or ''
    if e.get('failure_class')=='FRESH_ELABORATION_TIMEOUT': return 'FRESH_ELABORATION_TIMEOUT'
    if e['status']=='CONFIG_MISMATCH' or e.get('required_configuration')=='OFF': return 'CONFIG_OFF_REQUIRED'
    fbd=e.get('fresh_body') or '';gbd=e.get('gate_body') or ''
    if e['module']=='AspisR1TerminalDecoder.Funs' and err.startswith('fresh declaration'): return 'EXTERNAL_P_AXIOM'
    if err.startswith('blocked by failed callee'): return 'BLOCKED_BY_CALLEE'
    fl='loop' in fbd.split();gl='loop' in gbd.split()
    if fl!=gl or err.startswith('NOT ATTEMPTED'): return 'LOOP_ENCODING_OR_CALLER'
    dn=e.get('diff_normalized') or ''
    if 'array_from_fn_copy' in dn or 'core.array.from_fn' in dn: return 'ARRAY_FROM_FN_LIBRARY'
    if re.search(r'QM31\.(ZERO|ONE)|M31\.(ZERO|ONE)',dn): return 'CONST_MONADIC_BINDING'
    if 'timeout' in err: return 'HEARTBEAT_TIMEOUT'
    if err.startswith('fresh declaration (or a callee) did not elaborate'): return 'FRESH_DID_NOT_ELABORATE'
    a_=[t.replace('aspis_core.','') for t in fbd.split()];b_=[t.replace('aspis_core.','') for t in gbd.split()]
    if a_==b_: return 'BODY_EQUAL_UP_TO_CRATE_PREFIX_CALLEE_NOT_EQUATED'
    return 'OTHER'
recs={}   # (module, full) -> new record
eq_modules={}
nonfrozen=[]
for m,pl in PLAN.items():
    mm=dict(passes=[],reached={})
    eq_modules[m]=mm
    for ps in pl['passes']:
        lab=label(m,ps);st,rnd=latest(lab,'state');rp,rrnd=latest(lab,'report')
        g=EV/ps['gate'];gt=g.read_text()
        if ps.get('gate_namespace'): gt,_=G.extract_namespace(gt,ps['gate_namespace'])
        gb={b['name']:b for b in G.parse_blocks(gt) if b['kind']=='decl'}
        gall=dict(gb)
        for xg in ps.get('gate_extra') or []:
            for b in G.parse_blocks((EV/xg).read_text()):
                if b['kind']=='decl' and b['name'] not in gall: gall[b['name']]=b
        if ps.get('gate_types') and ps['kind']=='Funs':
            for b in G.parse_blocks((EV/ps['gate_types']).read_text()):
                if b['kind']=='decl' and b['name'] not in gall: gall[b['name']]=b
        k='Types.lean' if ps['kind']=='Types' else 'Funs.lean'
        ftxt=apply_rename((EV/ps['fresh_dir']/k).read_text(),ps.get('rename_fresh'))
        fb={b['name']:b for b in G.parse_blocks(ftxt) if b['kind']=='decl'}
        nm=ps.get('name_map') or {}
        pgns=ps['gns']
        mm['passes'].append(dict(label=lab,kind=ps['kind'],run=ps['run'],tool=ps['tool'],fresh_dir=ps['fresh_dir'],rename_fresh=ps.get('rename_fresh'),name_map=nm,gate=ps['gate'],gate_origin=ps['gate_origin'],state_round=rnd,skip_divergent=lab in ('RPu_FIq_Native10','RPu_FIq_Native13','RPu_FIq_Native14','RPu_FIq_Native14_p2')))
        vk=LAB2V.get(lab)
        resolved=set((rp or {}).get('names_resolved_to_gate_funs') or [])
        for full in ps['scope']:
            rel=full[len(pgns)+1:] if full.startswith(pgns+'.') else full
            # fresh name candidates
            cands=[rel,'aspis_core.'+rel,rel[len('aspis_core.'):] if rel.startswith('aspis_core.') else rel]
            fn=next((c for c in cands if c in fb),None)
            # state key after rename
            gn=nm.get(fn,fn) if fn else rel
            if gn not in gb and rel in gb: gn=rel
            required='OFF' if (gn in gb and re.search(r'wrapping_|Wrapping',gb[gn]['text'])) else 'ON'
            base=dict(module=m,definition=full,pass_label=lab,theorem=None,theorem_file=f"PRVEq_{lab}.lean",fresh_source=ps['fresh_dir'],fresh_run=ps['run'],aeneas_tool='aeneas-original-959659a6 (PCQG_ emission, ORIGINAL Aeneas; compiled against the gate-compatible Aeneas library)',
                      configuration='ON',required_configuration=required,fresh_overflow_checks_on=True,fresh_name=fn,gate_source=ps['gate'],verify_bundle=vk[0] if vk else None,verify_attempt=vk[1] if vk else None,state_round=rnd,decided_by='P2g')
            if fn and ps['kind']=='Funs' and fn in fb:
                _seen,_res,_axs=fresh_closure(fn,fb,set(gall),None,None)
                base['fresh_closure_mentions_opaque_P1f_names']=sorted({x for x in ('external_linear_lazy','empty_root') if any(x in t for q in _seen for t in G.lean_ident_tokens(fb[q]['body']))})
            if lab in RETIRED:
                e=dict(base,status='FAILED',failure_class='FRESH_ELABORATION_TIMEOUT',error=RETIRED[lab]['reason'],attempts=RETIRED[lab]['attempts'],basis_not_correct=False,basis_problems=[])
                if fn in fb and gn in gb: e['diff_normalized']=udiff(fb[fn],gb[gn])
                recs[(m,full)]=e;mm['reached'][full]=e;continue
            sd=st['defs'].get(fn) if st and fn else None
            ty=(rp or {}).get('types',{}).get(fn) if fn else None
            if fn is None:
                e=dict(base,status='NO_FRESH_EMISSION',reason='no declaration of this name (or prefix variant) in the planned PCQG_ emission after the recorded renames',basis_not_correct=True,basis_problems=['no fresh declaration'])
            elif sd is not None and sd['status']=='proved':
                thm=f"PRVEq.{m}{ps['tag']}.{fn}"
                isstruct=fb[fn]['dkind']=='structure'
                stt='PROVED_EQUIV' if isstruct else ('PROVED_RFL' if sd['stage']==1 else 'PROVED_UNFOLD')
                e=dict(base,status=stt,theorem=thm,statement=f"@{pgns}.PRVFresh_{lab}.{fn} = @{pgns}.{gn}")
                a=AX.get(vk[0],{}).get('axioms','') if vk else ''
                mx=re.search(r"'"+re.escape(thm)+r"(?:\.equiv)?' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",a)
                if mx:
                    axs=set(z.strip() for z in (mx.group(2) or '').split(',') if z.strip());e['axioms']=sorted(axs);e['axioms_ok']=axs<=OK_AX
                else: e['axioms']='NOT_FOUND_IN_VERIFY_RECEIPT';e['axioms_ok']=None
                if ps['kind']=='Funs':
                    seen,res,axs=fresh_closure(fn,fb,set(gall),None,None)
                    e['fresh_closure_size']=len(seen)
                    e['relative_to_gate_callees']=sorted(res&resolved)
                    e['conditional_on_fresh_axioms']=sorted(axs)
                    if axs or (res&resolved): e['conditional']=True
                e['basis_not_correct']=required!='ON';e['basis_problems']=[] if required=='ON' else ['gate body uses wrapping_*: required configuration OFF, emission is overflow-ON']
            elif sd is not None and sd['status']=='failed':
                e=dict(base,status='FAILED',failure_class=sd.get('class'),error=(sd.get('error') or '')[:400],callees=sd.get('callees'))
                if fn in fb and gn in gb:
                    e['diff_normalized']=udiff(fb[fn],gb[gn]);ops=opdiff(fb[fn],gb[gn])
                    e['fresh_body']=G.norm_decl(fb[fn])[:2500];e['gate_body']=G.norm_decl(gb[gn])[:2500]
                    ov=[o for o in ops if any(OV.search(t) for side in o for t in side)]
                    if ov:
                        e['status']='CONFIG_MISMATCH';e['config_mismatch_reason']='fresh (overflow-checks-on) and gate bodies differ in a checked/wrapping/overflowing/saturating operation';e['overflow_op_diff']=[[' '.join(s) for s in o] for o in ov][:6]
                e['basis_not_correct']=(required!='ON') or e['status']=='CONFIG_MISMATCH'
                e['basis_problems']=[] if not e['basis_not_correct'] else ['gate body is wrapping (required OFF) or differs in overflow operations from the overflow-ON emission; no matching-configuration P1f emission']
            elif ty is not None:
                e=dict(base,status='TEXT_IDENTICAL_ONLY' if ty['status']=='text_identical_only' else 'NOT_COMPARED',types_status=ty['status'],text_identical=ty.get('text_identical'),basis_not_correct=False,basis_problems=[])
            else:
                e=dict(base,status='FAILED',failure_class='NOT_IN_COMMON_DECLARATIONS',error='fresh declaration present but not among the compared common declarations (gate name differs or kind not compared)',basis_not_correct=False,basis_problems=[])
            recs[(m,full)]=e;mm['reached'][full]=e
for e in recs.values():
    if e['status'] in('FAILED','CONFIG_MISMATCH'): e['diff_class']=diff_class(e)
for m,pl in PLAN.items():
    for kind,names in (pl.get('uncovered') or {}).items():
        for full in names:
            if (m,full) in recs: continue
            e=dict(module=m,definition=full,status='NO_COMMON_LEAN_NAME',reason='the name is declared (non-axiom) in a PCQG_ run but is not a compared common declaration: the gate source of the module has no declaration under this name or prefix variant (planner cover test)',fresh_run=None,configuration='ON',required_configuration='ON',aeneas_tool='aeneas-original-959659a6',basis_not_correct=True,basis_problems=['no common declaration'],decided_by='P2g')
            recs[(m,full)]=e;eq_modules[m]['reached'][full]=e
# nonfrozen candidates: failed bodies whose diff is not an overflow-operation difference
for (m,full),e in recs.items():
    if e['status']=='FAILED' and e.get('diff_class')=='OTHER':
        nonfrozen.append(dict(module=m,definition=full,fresh_run=e['fresh_run'],diff_normalized=e['diff_normalized'][:900],note='candidate only: body differs from the frozen-source emission in a non-overflow way (or the error is a boundary); no frozen-revision test was run'))
# ---- merge into ALL_STATUS
new=copy.deepcopy(OLD);tot={}
changed=[];
def good(r): return r['status'].startswith('PROVED') and not r.get('basis_not_correct')
for (m,full),e in recs.items():
    old=new['modules'][m][full]
    e=dict(e);e.setdefault('basis_not_correct',False);e.setdefault('basis_problems',[])
    if e['status'] in('TEXT_IDENTICAL_ONLY','NOT_COMPARED'): e['basis_not_correct']=e.get('basis_not_correct',False)
    e['supersedes']=dict(tool=old.get('decided_by'),status=old['status'],basis_not_correct=old.get('basis_not_correct'),theorem=old.get('theorem'),fresh_emission=old.get('fresh_emission'))
    keep_old=good(old)   # an old PROVED record with a correct basis stands (it was not in the scope set)
    if keep_old: continue
    # old proved-but-incorrect-basis record is not lost: referenced in supersedes
    if (not good(e)) and old['status'].startswith('PROVED') and e['basis_not_correct']:
        # new record is itself basis-incorrect and not a proof: keep the old (real, Lean-checked, retained-emission) proof flagged as before, add the new attempt
        old['later_attempt_P2g']=dict(status=e['status'],fresh_run=e['fresh_run'],error=e.get('error'),config_mismatch_reason=e.get('config_mismatch_reason'),required_configuration=e['required_configuration'])
        continue
    new['modules'][m][full]=e;changed.append((m,full,old['status'],e['status']))
import collections
c=collections.Counter()
for m,r in new['modules'].items():
    for n,x in r.items(): c[x['status']]+=1
new['totals']=dict(c);new['schema']='PCUG_ALL_STATUS/1'
new['n_definitions']=sum(len(r) for r in new['modules'].values())
new['superseding_rule_P2g']=__doc__.split('Superseding rule (recorded in the output): ')[1]
new['p2g_changed']=len(changed)
new['decided_by']=dict(collections.Counter(x.get('decided_by') for r in new['modules'].values() for x in r.values()))
new['sources']=list(new.get('sources',[]))+['P2g: PCUG_EQ_STATUS.json (PCQG_ P1f emissions, original Aeneas 959659a6)']
new['target_established']=False
Path(H/'PCUG_ALL_STATUS.json').write_text(json.dumps(new,indent=1))
tot=collections.Counter(e['status'] for e in recs.values())
Path(H/'PCUG_EQ_STATUS.json').write_text(json.dumps(dict(schema='PCUG_EQ_STATUS/1',target_established=False,note='One record per scope definition (not PROVED on a correct basis in PCUF_ALL_STATUS and with a non-axiom declaration of the name in a PCQG_ run with exit 0). All emissions overflow-checks ON, ORIGINAL Aeneas 959659a6. PROVED_* = Lean equality @fresh = @gate-constant, verified in PCUG_L021/L022.',totals=dict(tot),verify_bundles=AX,modules=eq_modules),indent=1))
p3=[dict({k:v for k,v in e.items() if k not in('supersedes',)}) for (m,n),e in recs.items() if not e['status'].startswith('PROVED')]
Path(H/'PCUG_FOR_P3.json').write_text(json.dumps(dict(schema='PCUG_FOR_P3/1',target_established=False,items=p3),indent=1))
Path(H/'PCUG_NONFROZEN_CANDIDATES.json').write_text(json.dumps(dict(schema='PCUG_NONFROZEN_CANDIDATES/1',note='Candidates only; none confirmed against an older source revision.',items=nonfrozen),indent=1))
print(dict(tot));print(len(changed),'changed in ALL_STATUS');print(dict(c))
