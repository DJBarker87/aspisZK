#!/usr/bin/env python3
"""Builds PCQ_B_COVERAGE.json and PCQ_B_HAND_MODELS.json from committed PINS/emissions and gate sources (git show research:)."""
import json,re,subprocess,glob,hashlib,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def git(*a):return subprocess.run(['git','-C',str(E)]+list(a),capture_output=True,text=True).stdout
def show(path):
    r=subprocess.run(['git','-C',str(E),'show','research:'+path],capture_output=True,text=True);return r.stdout if r.returncode==0 else None
specs={s['spec_id']:s for s in json.load(open(E/'PCQ_extract_specs.json'))['specs']}
part=json.load(open(E/'PCQ_PARTITION.json'))['modules']
RUNS={'S016':'PCQ_E402','S020':'PCQ_E410','S015':'PCQ_E415','S017':'PCQ_E412','S021':'PCQ_E414','S022':'PCQ_E416'}
FAIL={'S019':'no successful run (E403, E409)','S018':'no run: no frozen counterpart'}
lock=git('show',REV+':Cargo.lock')
def crate_of(n):
    if n.startswith(('core.','alloc.','std.')):return 'rust std/core/alloc from the pinned nightly toolchain (charon-driver log: nightly-2026-06-01; PINS environment RUSTUP_TOOLCHAIN field: nightly-2026-09-17; both recorded, not reconciled here)'
    for pre,name in [('aspis_core.','aspis-core'),('aspis_statement.','aspis-statement')]:
        if n.startswith(pre):return name+' 0.1.0 (workspace path crate at frozen 4bb3b3f)'
    m=re.match(r'(solana_[a-z_0-9]+)\.',n)
    if m:
        c=m.group(1).replace('_','-');v=re.findall(r'name = "%s"\nversion = "([^"]+)"'%re.escape(c),lock);return c+' '+(','.join(v) if v else 'not found in Cargo.lock')
    return 'unresolved'
def fresh_text(run):
    d=glob.glob(str(E/(run+'_emitted/raw/*')))[0];return d,{f:((Path(d)/f).read_text() if (Path(d)/f).exists() else '') for f in ['Funs.lean','Types.lean','FunsExternal_Template.lean','TypesExternal_Template.lean']}
DEFRE=lambda n:re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*(def|abbrev|instance|axiom|opaque|structure|inductive|theorem)\s+(?:[\w.]*\.)?%s\b'%re.escape(n),re.M)
ALL=open('/private/tmp/claude-501/-Users-dominic-ZK/e51a42a3-64c9-4a23-9ea1-f7bf410e2db1/scratchpad/alltree.txt').read().split('\n')
BY={}
for q in ALL:
    if q.endswith('.lean'):BY.setdefault(q.rsplit('/',1)[-1],[]).append(q)
UNRES={}
def resolve(base,imp):
    fn=imp.replace('.','/')+'.lean';q=base+'/'+fn
    if show(q) is not None:return q
    c=BY.get(imp.split('.')[-1]+'.lean',[])
    if c:return sorted(c,key=lambda z:(z.rsplit('/',1)[0]!=base,z))[0]
    return None
def gate_files(mod):
    x=part[mod];paths=[p for c in x['candidates'] for p in c['paths']];seen={};todo=[(paths[0],0)];fam=paths[0].rsplit('/',1)[0]
    for sib in ('External',):
        q=paths[0].replace('Funs.lean',sib+'.lean').replace('Types.lean',sib+'.lean')
        if q!=paths[0]:todo.append((q,1))
    while todo:
        p,dep=todo.pop()
        if p in seen:continue
        t=show(p)
        if t is None:continue
        seen[p]=t
        if dep>=6 or '/Aeneas' in p:continue
        base=p.rsplit('/',1)[0]
        for imp in re.findall(r'^import ([\w.]+)',t,re.M):
            if imp in('Aeneas','Std','Lean','Mathlib') or imp.startswith(('Aeneas.','Std.','Lean.','Mathlib.','Init')):continue
            q=resolve(base,imp)
            if q is None:UNRES.setdefault(mod,set()).add(imp)
            elif q not in seen:todo.append((q,dep+1))
    return seen
cov={};hand={};gen={};nof={};ovl={};clo={}
for sid,s in specs.items():
    if s.get('p1_half')!='P1b' or not s['kind'].startswith('frozen') or s.get('pilot'):continue
    run=RUNS.get(sid);entries=[];
    if run:
        d,fr=fresh_text(run);pins=json.load(open(E/(run+'_emitted/'+run+'_PINS.json')))
        alltext=fr['Funs.lean']+fr['Types.lean']
        ext=fr['FunsExternal_Template.lean']+fr['TypesExternal_Template.lean']
    for dname in s['covers']['definitions']:
        suffix=dname.split('.',1)[1]
        if not run:
            entries.append(dict(gate_definition=dname,status='MISSING',reason=FAIL.get(sid,'no run')));continue
        m=DEFRE(suffix).search(alltext)
        if not m:
            for r2 in set(RUNS.values())-{run}:
                d2,f2=fresh_text(r2)
                if DEFRE(suffix).search(f2['Funs.lean']+f2['Types.lean']):
                    m=None;entries.append(dict(gate_definition=dname,status='COVERED',fresh_definition=suffix,emission_run=r2,note='covered by a sibling run of the same crate, not by this spec\'s own run'));break
            else:pass
            if entries and entries[-1]['gate_definition']==dname:continue
        if m:entries.append(dict(gate_definition=dname,status='COVERED',fresh_definition=suffix,fresh_file='Funs.lean' if m.group(0) in fr['Funs.lean'] else 'Types.lean',emission_run=run))
        else:
            ax=re.search(r'^axiom\s+%s\b'%re.escape(suffix),ext,re.M)
            entries.append(dict(gate_definition=dname,status='MISSING',reason=('fresh emission has only an opaque external axiom (Aeneas internal error on the body in the unrestricted shape, see failures)' if ax else 'not emitted by the fresh run (roots/opacity shape did not reach it)'),emission_run=run))
    cov[sid]=dict(spec_id=sid,label=s.get('label'),run=run,emission_dir=(run+'_emitted/raw/'+s['namespace'] if run else None),gate_modules=s['covers']['modules'],definitions=entries,llbc_sha256=(pins.get('llbc_sha256') if run else None))
    if run:
        names=re.findall(r'^axiom\s+([\w.]+)',ext,re.M)
        for mod in s['covers']['modules']:
            if mod not in part:continue
            files=gate_files(mod)
            names=re.findall(r'^axiom\s+([\w.]+)',fr['TypesExternal_Template.lean'],re.M) if mod.endswith('Types') else re.findall(r'^axiom\s+([\w.]+)',ext,re.M)
            fnames=set(re.findall(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev|axiom|structure|inductive|instance)\s+([\w.]+)',fr['Funs.lean']+fr['Types.lean']+ext,re.M))
            for p,tx in files.items():
                if 'AUTOMATICALLY GENERATED BY AENEAS' not in tx[:300] and '/Aeneas' not in p:clo.setdefault(mod,{})[p]=sorted(set(re.findall(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev|axiom|opaque|instance)\s+([\w.]+)',tx,re.M)))
            for p,tx in files.items():
                if 'AUTOMATICALLY GENERATED BY AENEAS' in tx[:300]:continue
                for mm in re.finditer(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev|axiom|opaque|structure|inductive|instance)\s+([\w.]+)',tx,re.M):
                    nm=mm.group(1);short=nm.split('FIo_Native.',1)[-1]
                    if short in fnames:
                        isax=bool(re.search(r'^axiom\s+%s\b'%re.escape(short),ext,re.M))
                        ovl.setdefault(mod,[]).append(dict(gate_module=mod,name=short,gate_file=p,gate_definition_exact_text='\n'.join(tx[mm.start():].split('\n')[:8]),fresh_form=('axiom in external template' if isax else 'Aeneas-emitted definition with body'),emission_run=run,pinned_crate=crate_of(short)))
            for n in names:
                hm=[];gm=[]
                for p,tx in files.items():
                    mm=DEFRE(n).search(tx)
                    if not mm:continue
                    (gm if 'AUTOMATICALLY GENERATED BY AENEAS' in tx[:300] else hm).append((p,tx,mm))
                form='axiom (Aeneas external template) in '+run+' '+('TypesExternal_Template.lean' if re.search(r'^axiom\s+%s\b'%re.escape(n),fr['TypesExternal_Template.lean'],re.M) else 'FunsExternal_Template.lean')
                if hm:
                    p,tx,mm=hm[0];hand.setdefault(mod,[]).append(dict(gate_module=mod,external_name=n,gate_file=p,gate_definition_exact_text='\n'.join(tx[mm.start():].split('\n')[:8]),fresh_form=form,pinned_crate=crate_of(n),emission_run=run))
                elif gm:gen.setdefault(mod,[]).append(dict(gate_module=mod,external_name=n,gate_file=gm[0][0],fresh_form=form,note='gate side is an Aeneas-generated body (not hand-written); fresh side is an opaque external at the crate boundary'))
                else:nof.setdefault(mod,[]).append(dict(gate_module=mod,external_name=n,fresh_form=form,pinned_crate=crate_of(n),note='no definition found in the gate file and its resolved import closure (git show research:); resolution is by file basename, see unresolved_gate_imports'))
json.dump(dict(schema='PCQ_B_COVERAGE/1',target_established=False,note='Coverage means the fresh frozen emission contains a definition of the same name; it is NOT an equality (P2/P3).',specs=cov),open(E/'PCQ_B_COVERAGE.json','w'),indent=1)
json.dump(dict(schema='PCQ_B_HAND_MODELS/1',target_established=False,note='Record only. For a *Types gate module only the fresh TypesExternal names are checked, otherwise all external names of the run. Externals of the fresh emission that the gate side defines by non-Aeneas-generated text. Searched gate file + transitive same-directory imports (closure resolved by import name, else unique basename search over the research tree). No trust rows added or proposed.',frozen_cargo_lock='4bb3b3f:Cargo.lock',modules=hand,gate_side_aeneas_generated_body_vs_fresh_external=gen,no_gate_definition_found=nof,hand_written_files_in_gate_closure_declared_names=clo,hand_written_gate_definitions_whose_name_is_emitted_by_fresh_run=ovl,unresolved_gate_imports={k:sorted(v) for k,v in UNRES.items()}),open(E/'PCQ_B_HAND_MODELS.json','w'),indent=1)
for sid,c in cov.items():print(sid,c['run'],[(d['gate_definition'].split('.')[-1],d['status']) for d in c['definitions']])
print({k:len(v) for k,v in hand.items()})
