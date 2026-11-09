#!/usr/bin/env python3
"""PCUC_hand_models.py: record (never add trust rows) every external name of the fresh emissions of this cluster and how the gate module defines it."""
import json,re,sys
from pathlib import Path
sys.dont_write_bytecode=True
import PCUC_gen_equalities as G
prep=json.load(open('gen_prepared.json'));P=json.load(open('PCUC_PARTITION.json'))['modules']
PIN={'aspis_core':'crate aspis-core (workspace path crate, frozen 4bb3b3f5; Cargo.lock path dependency, no registry version)',
     'atomic_statement':'crate aspis-statement (workspace path crate, frozen 4bb3b3f5)','pool_v1':'crate aspis-statement (workspace path crate, frozen 4bb3b3f5)',
     'core':'Rust core library of rustc nightly-2026-06-01 sysroot (no crate version; tool pin in the PCQ/PCQC PINS files)','Slice':'Rust core library (slice PartialEq impl), rustc nightly-2026-06-01 sysroot',
     'fast_pairing':'crate aspis-r1-cost-probe (programs/r1-cost-probe, frozen 4bb3b3f5)','verifier':'crate aspis-r1-cost-probe (programs/r1-cost-probe, frozen 4bb3b3f5)','MutAArray':'Aeneas std model of core::slice::IterMut (Aeneas library)'}
GATE_EXTRA={'AspisR1TerminalDecoder.Funs':['evidence/replay-dry3-20261026/RPz2_recovered/AspisR1TerminalDecoder/Types.lean','docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/FunsExternal.lean'],
            'NFY_Part043':['evidence/slice-s-retarget-20261104/NFY_L050/sources/NFY_generated/NFY_Part042.lean']}
import subprocess
def show(p):
    r=subprocess.run(['git','show','HEAD:'+p],capture_output=True);return r.stdout.decode('utf-8','replace') if r.returncode==0 else ''
entries=[]
for key,r in prep.items():
    m=r['module']
    for ps in r.get('passes',[]):
        lab=m.replace('.','_')+ps['tag'];rep=json.load(open(f'gen/PRVEq_{lab}.report2.json'));st=json.load(open(f'gen/PRVEq_{lab}.state2.json'))
        names=sorted(set((rep.get('external_funs') or [])+(rep.get('external_types') or [])+(rep.get('names_resolved_to_gate_funs') or [])))
        if not names: continue
        fdir=Path('inputs/fresh_'+lab);ext=''.join((fdir/n).read_text() for n in ('FunsExternal_Template.lean','TypesExternal_Template.lean') if (fdir/n).exists())
        gsrcs=[(ps['gate_path'],Path('inputs/gate_'+lab+'.lean').read_text())]+[(q,show(q)) for q in GATE_EXTRA.get(m,[])]
        gsrcs=[(a,G.uncomment(b)) for a,b in gsrcs]
        fb={b['name']:b for b in G.parse_blocks((fdir/('Types.lean' if ps['tag'].startswith('_T') else 'Funs.lean')).read_text()) if b['kind']=='decl'}
        reached=[n[len(rep['gate_namespace'])+1:] for n in P[m]['reached_definitions']]
        for nm in names:
            fm=re.search(r'(?:/-[^\n]*?-/\n)?(?:/--(?:(?!-/).)*-/\n)?(?:@\[[^\n]*\]\n)?[^\n]*axiom '+re.escape(nm)+r'\b[^\n]*',ext,re.S)
            ftxt=None
            mm=re.search(r'((?:@\[[^\n]*\]\s*)*axiom '+re.escape(nm)+r'\b[^\n]*(?:\n[ \t]+[^\n]*)*)',ext)
            ftxt=mm.group(1) if mm else None
            hits=[]
            for path,txt in gsrcs:
                for gm in re.finditer(r'(?m)^((?:@\[[^\n]*\]\s*)*(def|abbrev|axiom|opaque|instance|structure|inductive|noncomputable def)\s+'+re.escape(nm)+r'\b[^\n]*(?:\n[ \t]+[^\n]*){0,4})',txt):
                    hits.append(dict(file=path,form=gm.group(2),text=gm.group(1)[:700]))
                if hits: break
            # also the gate-namespace-qualified name (gate namespace prefix may be implicit)
            dep=[n for n,b in fb.items() if re.search(re.escape(nm)+r'\b',b['body'])]
            def clo(seed):
                seen=set(seed);ch=True
                while ch:
                    ch=False
                    for n,x in st['defs'].items():
                        if n not in seen and any(c in seen for c in (x.get('callees') or [])): seen.add(n);ch=True
                return seen
            dr=sorted(n for n in clo(dep) if n in reached)
            top=nm.split('.')[0]
            gform=sorted({h['form'] for h in hits})
            entries.append(dict(gate_module=m,pass_label=lab,external_name=nm,fresh_form=dict(file=str(fdir),text=ftxt),gate_hits=hits,gate_form=gform,
                hand_model=bool(hits) and any(f!='axiom' for f in gform),
                origin=('gate defines it (def/abbrev/instance) where the fresh emission has only an opaque external axiom (extraction-scope difference or hand model; record only)' if hits and any(f!='axiom' for f in gform) else ('gate has an axiom of the same name' if hits else 'not defined in the gate module source or its Types/External sources: resolves to a gate-environment constant (imported module or Aeneas library) by name')),
                pinned_crate=PIN.get(top,'unknown (see name)'),dependent_reached_definitions=dr))
Path('PCUC_HAND_MODELS.json').write_text(json.dumps(dict(schema='PCUC_HAND_MODELS v1',target_established=False,note='Record only. No trust row proposed or added. Entries: every external name (fresh External template axiom or name resolved to a gate constant) per gate module and pass.',entries=entries),indent=1))
print(len(entries),sum(1 for e in entries if e['hand_model']))
for e in entries: print(e['pass_label'],e['external_name'],e['gate_form'],len(e['dependent_reached_definitions']))
