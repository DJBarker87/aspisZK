#!/usr/bin/env python3
"""PCUA_hand_models.py: build PCUA_HAND_MODELS.json (record only). For each job and each external name of the fresh emission
(axiom in its External template) that is not itself defined by the fresh namespace: the gate definition (exact text from the gate
source), whether that text is Aeneas-generated (doc comment with Rust path and Source line) or hand-written, the fresh axiom text,
the pinned crate and the dependent reached definitions."""
import sys,json,re
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;sys.path.insert(0,str(H))
import PCUA_gen_equalities as G, PCUA_jobs as J
st=json.loads((H/'PCUA_JOB_STATUS.json').read_text())['jobs']
GATEFILE={'RPz7_FIp_DotDecode':'evidence/replay-dry8-20261026/RPz7_FIp_DotDecode.lean','RPz7_FIp_NativeDots':'evidence/replay-dry8-20261026/RPz7_FIp_NativeDots.lean',
 'RPz7_FIo_NativeFuns':'evidence/replay-dry8-20261026/RPz7_FIo_NativeFuns.lean','RPz7_FIo_NativeTypes':'evidence/replay-dry8-20261026/RPz7_FIo_NativeTypes.lean',
 'Stage2ContinuationTypes':'docs/research/100bit-spend-path-20261013/lean/Stage2ContinuationTypes.lean','S1M31EmbeddingSourceV1':'evidence/port17release-20261024/dependency-source/S1M31EmbeddingSourceV1.lean',
 'AspisR1CurrentWide.Types':'docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Types.lean',
 'AspisR1CurrentWide.Funs':'docs/research/100bit-spend-path-20261013/evidence/session-b-current-wide-arithmetic-20261020/sources/AspisR1CurrentWide/Funs.lean'}
SRC=[H/'gate_src'/f for f in ['RPz7_FIo_NativeFuns.lean','RPz7_FIo_NativeTypes.lean','RPz7_FIp_DotDecode.lean','RPz7_FIp_NativeDots.lean','RPz7_FIo_NativeExternal.lean','Stage2ContinuationTypes.lean','S1M31EmbeddingSourceV1.lean','CW_Funs_sources.lean','CW_Types_sources.lean']]
def crate_of(name):
    if name.startswith('aspis_core.'):return 'aspis-core (workspace member of the frozen tree 4bb3b3f; Cargo.lock aspis-core 0.x path dependency)'
    if name.startswith(('core.','MutAArray','alloc.')):return 'rust core/alloc of the toolchain used by Charon (nightly; label mismatch recorded in PCQ_B_CLASSIFICATIONS B-7)'
    return 'aspis-r1-cost-probe (workspace member of the frozen tree 4bb3b3f)'
def find_gate(name):
    hits=[]
    for p in SRC:
        t=p.read_text();ns=re.findall(r'(?m)^namespace\s+(\S+)',t)
        for b in G.parse_blocks(t):
            if b['kind']=='decl' and b['name']==name:
                gen=bool(re.search(r'/--\s*(Trait implementation: )?\[[A-Za-z0-9_]+::',b['text'])) and 'Source:' in b['text']
                hits.append(dict(gate_source=p.name,namespace=ns[0] if ns else None,aeneas_generated_text=gen,gate_definition_text=b['text'].strip()[:1500]))
    return hits
def fresh_axiom(fresh,name):
    for f in ['FunsExternal_Template.lean','TypesExternal_Template.lean']:
        p=Path(fresh)/f
        if p.exists():
            t=p.read_text()
            m=re.search(r'(?m)^(?:@\[[^\]]*\]\s*)*axiom\s+'+re.escape(name)+r'\b.*?(?=\n\n|\Z)',t,re.S)
            if m:return f,m.group(0).strip()[:600]
    return None,None
out=[];seen=set()
for jid,r in st.items():
    j=J.JOBS[jid]
    if jid=='CtlCWFuns':continue
    dep={}
    for e in r['definitions']:
        for x in e.get('reaches_external_boundaries',[]):dep.setdefault(x,[]).append(e['definition']+' ['+e['status']+']')
    names=sorted(set((r['external_funs'] or [])+(r['external_types'] or [])))
    for n in names:
        key=(r['gate_module'],n,jid)
        f,ax=fresh_axiom(j['fresh'],n)
        hits=find_gate(n)
        out.append(dict(job=jid,gate_module=r['gate_module'],gate_file=GATEFILE.get(r['gate_module']),external_name=n,
            resolved_to_gate_constant_by_name=n in (r['names_resolved_to_gate_funs'] or []),fresh_form=('axiom in '+f+' of '+r['fresh_dir']) if f else 'not an axiom in this emission template (see note)',fresh_axiom_text=ax,
            gate_definitions_found=hits or None,pinned_crate=crate_of(n),dependent_reached_definitions_in_this_job=dep.get(n,[]),
            note=('gate side defined by Aeneas-generated text (not hand-written); fresh side opaque at the crate boundary' if hits and all(h['aeneas_generated_text'] for h in hits) else 'gate side text is not Aeneas-generated or was not found in the module sources; see gate_definitions_found' if hits else 'no gate definition of this name found in the module sources (the name does not resolve in the gate)')))
(H/'PCUA_HAND_MODELS.json').write_text(json.dumps(dict(schema='PCUA_HAND_MODELS/1',target_established=False,
 note='Record only; no trust rows added or proposed. An external name of a fresh emission (axiom in its External template) that the generated file resolves, by name, to the gate constant. A theorem that reaches such a name (field dependent_reached_definitions_in_this_job) is conditional on the gate constant being the intended model of the Rust item at that boundary; that is not proved here.',
 frozen_cargo_lock='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:Cargo.lock',entries=out),indent=1))
print(len(out),'entries;',sum(1 for o in out if not o['gate_definitions_found']),'without a gate definition in module sources;',sum(1 for o in out if o['gate_definitions_found'] and not all(h['aeneas_generated_text'] for h in o['gate_definitions_found'])),'with non-generated gate text')
