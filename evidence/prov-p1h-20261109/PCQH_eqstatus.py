#!/usr/bin/env python3
"""PCQH_eqstatus.py: build PCQH_EQ_STATUS.json (this job's equality records) from the final generator reports, the r0.transport.order
file, the constant file, and the verifying receipts."""
import json,re,sys,glob,collections
from pathlib import Path
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;EV=H.parent
plan=json.load(open(H/'PCQH_PLAN.json'))
cov=json.load(open(EV/'prov-p1g-20261109/PCQD_COVERAGE.json'))
tool={}
for e in cov['entries']:
    for x in e.get('evidence') or []:
        if isinstance(x,dict) and 'run' in x: tool[x['run']]=x['tool']
FINAL={ # label -> (final report round, verifying scope, bundle)
 'AdapterRwModel':(2,'PCQH_L019','PRVEq_bundle_B12'),'AspisR1DecodeKFullV10_Funs':(2,'PCQH_L019','PRVEq_bundle_B12'),'NGN_Emitted':(2,'PCQH_L019','PRVEq_bundle_B12'),
 'Port4C_NativePrefix':(2,'PCQH_L019','PRVEq_bundle_B12'),'Port5Q2_ReaderWeights':(2,'PCQH_L019','PRVEq_bundle_B12'),'NJA_CountBody':(2,'PCQH_L019','PRVEq_bundle_B12'),
 'AspisR72Sampler_Funs':(3,'PCQH_L032','PRVEq_bundle_B25'),'AspisR72Sampler_Types':(2,'PCQH_L032','PRVEq_bundle_B25'),
 'CurrentCompactCallerTypesV1':(2,'PCQH_L032','PRVEq_bundle_B25'),'CurrentCompactCallerTypesV1_p2':(2,'PCQH_L032','PRVEq_bundle_B25'),
 'CurrentCompactCallerTypesV1_p3':(2,'PCQH_L032','PRVEq_bundle_B25'),'CurrentCompactCallerTypesV1_p4':(2,'PCQH_L032','PRVEq_bundle_B25'),
 'NFN_ExtractedGeometry':(4,'PCQH_L033','PRVEq_bundle_B35'),'NFN_ExtractedGeometry_p2':(4,'PCQH_L033','PRVEq_bundle_B35'),'NFN_ExtractedGeometry_p3':(2,'PCQH_L033','PRVEq_bundle_B35'),
 'Port3_NativeGeometryBody':(2,'PCQH_L033','PRVEq_bundle_B35'),
 'AspisR1AdapterReconstruct_Funs':(2,'PCQH_L034','PRVEq_bundle_B45'),'AspisR1AdapterReconstruct_Types':(2,'PCQH_L034','PRVEq_bundle_B45'),'S1NativeCompactModelV1':(3,'PCQH_L034','PRVEq_bundle_B45')}
HAND_ADAPTED_MODULES={'AdapterRwModel':'gate functions are parametric in the hand-written boundary record AdapterRw.Ops (gate takes `ops`), the fresh emission calls the SDK/cross-crate externals as axioms; not comparable as functions',
 'Port3_NativeGeometryBody':'gate functions are parametric in the hand-written record Ops (callbacks for field/domain operations) and its carrier types differ (aspis_core.field.CM31/M31, r0.Error, verifier.QueryGeometry); fresh calls concrete functions',
 'Port4C_NativePrefix':'gate functions are parametric in the hand-written record Leaves; carrier types differ',
 'Port5Q2_ReaderWeights':'gate functions are parametric in CheckpointBytes4Sections.ReadK and use a hand-written IterMut model; carrier types differ'}
def gate_block(gpath,name):
    t=(EV/gpath).read_text()
    m=re.search(r'(?m)^(?:@\[[^\n]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev)\s+'+re.escape(name)+r'(?=[\s(:])',t)
    if not m: return ''
    n=re.search(r'\n\n(?=/--|@\[|def |structure|inductive|abbrev|#print|end )',t[m.end():])
    return t[m.start():m.end()+(n.start() if n else len(t))]
recs=[]
for m,v in plan.items():
    for ps in v['passes']:
        lab=(m.replace('.','_')+ps['tag']); rnd,scope,bundle=FINAL[lab]
        rep=json.load(open(H/f'gen/PRVEq_{lab}.report{rnd}.json'))
        gns=rep['gate_namespace']; nm=rep['name_map']
        rt=tool.get(ps['run'],'?')
        for n,p in rep['per_definition'].items():
            gname=nm.get(n,n); gblock=gate_block(ps['gate'],gname) if ps['kind']=='Funs' or True else ''
            wrap=bool(re.search(r'wrapping_|\.wrapping',gblock))
            st=p['status']; why=p.get('error') or ''
            if st in('proved','given'):
                r=dict(status='EQUALITY_PROVED',stage=p.get('stage'),given=(st=='given'))
            else:
                if m in HAND_ADAPTED_MODULES: cls='HAND_ADAPTED';why=HAND_ADAPTED_MODULES[m]+' | last probe: '+why[:120]
                elif wrap: cls='CONFIG_MISMATCH'
                elif 'did not elaborate' in why: cls='FRESH_NOT_ELABORATED'
                elif 'timeout' in why: cls='OPEN_TWO_FAILED_SHAPES_HEARTBEAT'
                elif 'blocked by failed callee' in why: cls='BLOCKED_BY_CALLEE'
                else: cls='OPEN_UNSOLVED'
                r=dict(status='OPEN',reason_class=cls,reason=why[:300])
            r.update(module=m,label=lab,definition=f'{gns}.{gname}',fresh_name=n,kind=ps['kind'],gate_requires_wrapping_ops=wrap,
                     theorem=f'PRVEq.{lab}.{n}',proving_file=f'PRVEq_{lab}.lean',verifying_scope=scope,verifying_bundle=bundle+'.lean',
                     fresh_run=ps['run'],aeneas_tool=rt,fresh_dir=ps['fresh_dir'],configuration_fresh='ON',
                     required_configuration=('OFF (gate body uses wrapping operators)' if wrap else 'ON'))
            recs.append(r)
        for n,t in (rep.get('types') or {}).items():
            gname=nm.get(n,n)
            s=t['status']
            if s.startswith('lean_eq') or s.startswith('lean_equiv'): rs='EQUALITY_PROVED'
            elif s=='external_instantiated': rs='OPEN'
            else: rs='OPEN'
            recs.append(dict(status=rs,reason_class=None if rs=='EQUALITY_PROVED' else ('TEXT_IDENTICAL_ONLY' if s=='text_identical_only' else s),module=m,label=lab,definition=f'{gns}.{gname}',fresh_name=n,kind='type',
                 type_status=s,text_identical=t.get('text_identical'),theorem=f'PRVEq.{lab}.{n}'+('.equiv' if 'equiv' in s else '') if rs=='EQUALITY_PROVED' else None,
                 proving_file=f'PRVEq_{lab}.lean',verifying_scope=scope,verifying_bundle=bundle+'.lean',fresh_run=ps['run'],aeneas_tool=rt,fresh_dir=ps['fresh_dir'],configuration_fresh='ON',required_configuration='ON'))
# r0.transport.order group (PRVEq_r0_transport_order.lean, PCQH_L014)
for n,thm in [('PADS','PADS_eq'),('PIVOT','PIVOT_eq'),('PAD_ROWS','PAD_ROWS_eq'),('order_loop0_loop0.body','order_loop0_loop0_body_eq'),('order_loop0_loop0','order_loop0_loop0_eq'),
              ('order_loop0.body','order_loop0_body_eq'),('order_loop0','order_loop0_eq'),('order','order_eq')]:
    recs.append(dict(status='EQUALITY_PROVED',module='RPz7_FIo_NativeFuns',label='r0_transport_order',definition=f'FIo_Native.aspis_core.r0.transport.{n}',fresh_name=f'r0.transport.{n}',kind='def',
        theorem=f'PRVEq.order.{thm}',proving_file='PRVEq_r0_transport_order.lean',verifying_scope='PCQH_L014',fresh_run='PCQE_E001',aeneas_tool='aeneas-original-959659a6',
        fresh_dir='prov-p1d-20261109/PCQE_E001_emitted/raw/PCQE_aspis_core_r0_transport',configuration_fresh='ON',gate_requires_wrapping_ops=(n!='PADS' and n!='PIVOT' and n!='PAD_ROWS'),
        required_configuration='OFF (gate loop bodies use wrapping_add)' if 'loop' in n or n=='order' else 'ON',
        note='fresh checked +1 on j and r = gate wrapping_add; equal as functions on ALL inputs (no caller domain needed): r+1 under guard r<PIVOT=1023; j+1 after Array.update out j i (success implies j<1024); generic lemmas PRVH.usize_add_one_wrap, PRVH.update_ok_lt'))
json.dump(dict(schema='PCQH_EQ_STATUS/1',target_established=False,frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',
  note='statements are fresh = gate against compiled gate constants of ledger30; verifying scopes are the final bundle compiles (exit 0, standard axioms only, receipts PCQH_Lnnn/receipt.json). OPEN records carry the reason class; none of them is a counterexample unless stated.',
  counts=dict(collections.Counter(r['status'] for r in recs)),records=recs),open(H/'PCQH_EQ_STATUS.json','w'),indent=1)
print(collections.Counter(r['status'] for r in recs)); print(collections.Counter((r['module'],r['status']) for r in recs if r['status']=='OPEN').most_common(40))
