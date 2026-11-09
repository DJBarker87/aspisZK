#!/usr/bin/env python3
"""PCUA_eqstatus.py: aggregate PCUA_JOB_STATUS.json + survey + partition into PCUA_EQ_STATUS.json (every reached definition of every
hub-cluster module) and PCUA_FOR_P3.json (every non-proved definition with its cause)."""
import sys,json,re
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;EV=H.parent
P=json.loads((H/'PCUA_PARTITION.json').read_text())['modules']
S=json.loads((H/'PCUA_SURVEY.json').read_text())
JS=json.loads((H/'PCUA_JOB_STATUS.json').read_text())['jobs']
ATT={json.loads(l)['attempt']:json.loads(l) for l in (H/'PCUA_ATTEMPTS.jsonl').read_text().splitlines() if '"event": "result"' in l}
FAIL=json.loads((EV/'prov-p1b-20261109/PCQ_B_FAILURES.json').read_text())
P0=json.loads((EV/'prov-p0-20261109/PCO_PILOT.json').read_text())['modules']['AdapterRwTypes']
MODS=['AspisR1CurrentWide.Types','AspisR1CurrentWide.Funs','CurrentWideMulCanonical','CurrentWideEqSemanticV7','AspisR1CanonicalQRawUnified.Types','AspisR1CanonicalQRawUnified.Funs','AdapterRwTypes','Stage2ContinuationTypes','S1M31EmbeddingSourceV1','RPz7_FIo_NativeTypes','FIo_QRawTypes','FIo_QRawFuns','RPz7_FIo_NativeExternal','RPz7_FIo_NativeFuns','RPz7_FIp_DotDecode','RPz7_FIp_NativeDots']
RANK={'PROVED_RFL':0,'PROVED_UNFOLD':1,'PROVED_EQUIV':2,'FAILED':3}
CUT={'AspisR1CanonicalQRawUnified.Types','AspisR1CanonicalQRawUnified.Funs','FIo_QRawTypes','FIo_QRawFuns','CurrentWideMulCanonical'}
def rel(M,n):
    ns=P[M].get('namespace')
    return n
def no_fresh(M,dn,info):
    r=info['rust']
    if M in CUT:return 'NO_FRESH_EMISSION','cut crate / transformed copy: the item has no frozen counterpart ('+r+'); routed to P4 (PRV_REPORT: QRaw canonical::raw and Mul-canonical items belong to cut crates)'
    for f in FAIL['failures']:
        if f['spec'] in ('S016','S022') and M in ('RPz7_FIo_NativeFuns','RPz7_FIo_NativeTypes'):
            for x in f['definitions']:
                if (x.startswith('...') and dn.endswith(x[3:])) or dn==x:
                    return 'NO_FRESH_EMISSION','P1b failure list '+f['spec']+' ('+', '.join(f['runs'])+'): '+f['error'][:160]
    if re.search(r'PartialEq',r) and M=='CurrentWideEqSemanticV7':return 'NO_FRESH_EMISSION','no standalone `eq` definition of the aspis-core field types exists in any fresh frozen emission checked (E009 has only the impl_def instance form); aspis-core emission under P1a is pending'
    return 'NO_FRESH_EMISSION','no fresh frozen emission contains the Rust item '+r+' (aspis-core / probe items: P1a pending, or P1b selection not run; no extraction scope in this job)'
rows={};allfail=[]
for M in MODS:
    reached=P[M]['reached_definitions'];ns=None
    jobs=[j for j in JS.values() if j['gate_module']==M and j['job']!='CtlCWFuns']
    res=[]
    for dn,info in reached.items():
        best=None;allj=[]
        for jb in jobs:
            for e in jb['definitions']:
                nm=e['definition']
                if dn==nm or dn.endswith('.'+nm):
                    allj.append((jb['job'],e))
        if M=='AdapterRwTypes':
            t=[x for x in P0['types'] if dn.endswith(x['definition'].split('.',1)[-1]) or x['definition'].endswith(dn.split('.',1)[-1])]
            ent=dict(gate_definition=dn,rust=info['rust'],prv_coverage=info['coverage'],source='P0 reuse (PCO_PILOT.json AdapterRwTypes; not redone)')
            if t:
                ent.update(status='REUSED_FROM_P0:'+t[0]['result'],p0_entry=t[0])
            else:ent.update(status='REUSED_FROM_P0:no_matching_entry')
            res.append(ent);continue
        ent=dict(gate_definition=dn,rust=info['rust'],prv_coverage=info['coverage'])
        if allj:
            allj.sort(key=lambda x:RANK.get(x[1]['status'],9))
            jb,e=allj[0];ent.update(status=e['status'],job=jb,fresh_emission=JS[jb]['fresh_dir'],generated_file=JS[jb]['generated_file'],final_scope=JS[jb]['final_scope'],
                conditional_on_external_boundaries=e.get('reaches_external_boundaries') or None,
                also_attempted=[dict(job=a,status=b['status']) for a,b in allj[1:]] or None)
            if e['status']=='FAILED':
                ent.update(error_class=e['error_class'],first_failing_goal_or_error=e.get('first_failing_goal_or_error') or e.get('reason'),first_failing_fresh_declaration=e.get('first_failing_fresh_declaration'),
                           normalized_text_diff_gate_to_fresh=e.get('normalized_text_diff_gate_to_fresh'),blocked_by=e.get('blocked_by'),statement=f"@{JS[jb]['generated_file']} :: PRVFresh_{M.replace('.','_')}.{e['definition']} = {M}.{e['definition']} (gate constant)")
        else:
            fr=S[M][dn]['fresh']
            if fr:
                k='Types.lean' if M.endswith('Types') else 'Funs.lean'
                fr=[f for f in fr if f.endswith('/'+k)]
            tinfo=[]
            for jb in jobs:
                rep=json.loads((H/('PRVEq_'+jb['job']+'.report.json')).read_text())
                for tn,tv in (rep.get('types') or {}).items():
                    if dn==tn or dn.endswith('.'+tn):tinfo.append((jb['job'],tv))
            tinfo=[x for x in tinfo if x[1]['status'] in ('text_identical_only','differs')]
            if tinfo:
                ident=[x for x in tinfo if x[1]['status']=='text_identical_only']
                x=(ident or tinfo)[0]
                ent.update(status='TEXT_IDENTICAL_ONLY' if ident else 'TYPE_TEXT_DIFFERS',job=x[0],fresh_emission=JS[x[0]]['fresh_dir'],generated_file=JS[x[0]]['generated_file'],
                    reason='inductive or non-simple structure: the generator emits no Lean theorem (text identity of the normalized declaration to the fresh emission only); not a proof of equality' if ident else 'normalized declaration text differs from the fresh emission; no Lean theorem generated',
                    also_text_identical_in=[y[0] for y in ident[1:]] or None)
            elif fr:
                ent.update(status='FRESH_EMISSION_EXISTS_NOT_PAIRED',fresh_candidates=fr[:4],reason='a same-named Rust item exists in a fresh frozen emission but the generator did not pair it with the gate declaration: either the fresh declaration name differs from the gate name by a crate prefix (aspis_core.* vs field.*), or the declaration kind is not def/abbrev/simple structure (inductive, instance, class: text-identity only), or the emission was not selected for this module in this job')
            else:
                s,why=no_fresh(M,dn,info);ent.update(status=s,reason=why)
        res.append(ent)
    rows[M]=res
cnt={}
for M,res in rows.items():
    c={}
    for e in res:c[e['status'].split(':')[0]]=c.get(e['status'].split(':')[0],0)+1
    cnt[M]=c
(H/'PCUA_EQ_STATUS.json').write_text(json.dumps(dict(schema='PCUA_EQ_STATUS/1',target_established=False,
  note='Per reached definition of each hub-cluster gate module. PROVED_* means a Lean theorem PRVFresh.f = Gate.f (or a generated Equiv for PROVED_EQUIV) compiled in the named final scope with only propext/Classical.choice/Quot.sound; conditional_on_external_boundaries lists fresh External-template names that the generated file resolves by name to gate constants (hand-model record PCUA_HAND_MODELS.json): such a theorem is conditional on that boundary. Not proved: anything not PROVED_*.',
  counts=cnt,modules=rows),indent=1))
print(json.dumps(cnt,indent=0))
