#!/usr/bin/env python3
"""Audit all ordinary experiments, including rejected implementations."""
import argparse,ast,hashlib,json,re
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2]
e=root/'evidence/r62-ordinary';parent=root/'evidence/r61-opening'
base='23cf1bd882ccce6f330a4cafb6d39e54c748b984';ex='docs/research/v8-no-work-100-20260907/experiments/'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def metrics(p):
    s=p.read_text();assert '\tExit status: 0' in s and '\tSwaps: 0' in s,p
    assert not re.search(r'^error(?:\[|:)',s,re.M),p
    t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s).group(1).split(':')
    return {'exit':0,'swaps':0,'wall_seconds':round(sum(float(x)*60**i for i,x in enumerate(reversed(t))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s).group(1))}
def normal(t):return {re.sub(r'::h[0-9a-f]+$','',x['name']):x['instructions']for x in t['functions']}
pm=json.loads((parent/'r18-stage.json').read_text());oldsvm=json.loads((parent/'r24-svm-a/receipt.json').read_text())
oldtrace=json.loads((parent/'full-trace/analysis.json').read_text());before=normal(oldtrace)
changes={ex+n for n in ['r19_channel_ordinary.rs','r22_scalar.rs','r27_native.rs','r27_check.rs']}
for n in changes:assert sha(e/'control'/n)==pm['files'][n]
control={Path(n).name:(e/'control'/n).read_text()for n in changes}
support_path=e/'control'/ex/'r18_minimal_support.rs'
assert sha(support_path)==pm['files'][ex+'r18_minimal_support.rs']
support=ast.literal_eval(re.search(r'SUPPORT: \[usize;163\] = (\[.*?\]);',support_path.read_text())[1])
assert len(support)==len(set(support))==163
scalar_loop='''    for i in 0..163 {
        let row=SUPPORT[i];let group=row>>4;let low=row&15;let value=delta[i];
        selected[low]=selected[low].add(value.mul(hb[group]));
        if low<3 {selected[16+low]=selected[16+low].add(value.mul(hb[64+group]));}
    }'''
reports={};pins={}
for variant in ['pair','gather-old','gather-checked']:
    d=e/variant;m=json.loads((d/'r18-stage.json').read_text())
    assert len(m['files'])==197 and set(m['files'])==set(pm['files'])
    assert {n for n,h in m['files'].items()if pm['files'][n]!=h}==changes
    for n in changes:assert sha(d/'source'/n)==m['files'][n]
    meta=m['r62_entry'if variant=='pair'else'r62_gather']
    assert meta['base_revision']==base and meta['control_manifest_sha256']==sha(parent/'r18-stage.json')
    assert meta['reference_entry_unchanged'] and not meta['protocol_changed'] and not meta['validation_removed']
    sources={Path(n).name:(d/'source'/n).read_text()for n in changes}
    if variant=='pair':
        assert meta['scalar_sites']==2
        assert sources['r19_channel_ordinary.rs']==control['r19_channel_ordinary.rs']+'\n'+(root/'tools/r62_entry.rs').read_text()
        assert sources['r22_scalar.rs']==control['r22_scalar.rs'].replace('entry(factors,0,','r62_entry(factors,')
        extra='r19_channel_ordinary::r62_entry_check(x);'
        tag='R62_ENTRY entry_coordinate_comparisons=262144 source_vectors=256'
    else:
        assert meta['products']==181 and meta['outputs']==19 and meta['max_dot_terms']==30 and meta['scratch_reuses_dead_factors']
        assert meta.get('checked_dot',False)==(variant=='gather-checked')
        # Exact source polynomial inventory. Tables encode all and only the
        # original (output, delta-index, hb-index) products in original order.
        rows=[];groups=[];ends=[0]
        for low in range(19):
            for i,row in enumerate(support):
                if row%16==(low if low<16 else low-16):rows.append(i);groups.append(row//16+(0 if low<16 else 64))
            ends.append(len(rows))
        tables='\n'.join(f'const R62_{n}:[usize;{len(v)}]={v};'for n,v in [('ENDS',ends),('ROWS',rows),('GROUPS',groups)])+'\n'
        helper=(root/'tools/r62_gather.rs').read_text()
        if variant=='gather-checked':helper=helper.replace('out[low]=corelib::field::qm31_dot(&left[..n],&right[..n]);','out[low]=corelib::field::r25_checked_dot(&left[..n],&right[..n])\n            .unwrap_or_else(||corelib::field::qm31_dot(&left[..n],&right[..n]));')
        assert sources['r19_channel_ordinary.rs']==control['r19_channel_ordinary.rs']+'\n'+tables+helper
        expected=control['r22_scalar.rs'].replace('    let wp=entry(factors,0,1023);\n','')
        assert expected.count(scalar_loop)==1
        expected=expected.replace(scalar_loop,'    let wp=entry(factors,0,1023);\n    r62_gather(delta,hb,factors,&mut selected);')
        assert sources['r22_scalar.rs']==expected
        extra='r19_channel_ordinary::r62_gather_check(x);'
        tag='R62_GATHER gathered_outputs=4864 source_vectors=256'
    assert sources['r27_native.rs']==control['r27_native.rs'].replace('r19_channel_ordinary::r27_tensor_check(x);','r19_channel_ordinary::r27_tensor_check(x);'+extra)
    assert sources['r27_check.rs']==control['r27_check.rs'].replace('R27_SPARSE source_vectors=256',tag)
    logs={}
    for kind,names in [('host',['ordinary-compile','ordinary-check','compile','wire-controls','world0','world1']),('sbf',['compile']),('svm',['world0','world1'])]:
        env=json.loads((d/f'r24-{kind}-a/environment.json').read_text())
        assert env['source_manifest_sha256']==sha(d/'r18-stage.json') and env['CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS']=='true'
        for n in names:logs[f'{kind}/{n}']=metrics(d/f'r24-{kind}-a'/(n+'.log'))
    log=(d/'r24-host-a/ordinary-check.log').read_text();assert tag in log
    for marker in ['tensor_coordinates=12032','poison_unused_coordinates=8448','genuine_public_inputs=2','image_retained=true T_unchanged=true auxiliary_proof=false']:assert marker in log
    wire=json.loads((d/'r24-host-a/wire-controls/results.json').read_text())
    assert len(wire['cases'])==3281 and sum(x['checked_rejection']for x in wire['cases'])==3280 and all(x['exit']==0 for x in wire['cases'])
    for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in (d/f'r24-host-a/world{w}.log').read_text()
    build=(d/'r24-sbf-a/compile.log').read_text()
    assert 'overflows the maximum allowed frame' not in build and not ('Stack offset' in build and 'exceeded' in build)
    svm=json.loads((d/'r24-svm-a/receipt.json').read_text())
    assert svm['source_manifest_sha256']==sha(d/'r18-stage.json') and svm['elf_sha256']==json.loads((d/'r24-sbf-a/environment.json').read_text())['elf_sha256']
    assert svm['driver_sha256']==oldsvm['driver_sha256'] and svm['full_verifier'] and not svm['instrumented']
    cu=[];assert len(svm['runs'])==2
    for i,r in enumerate(svm['runs']):
        assert r['world']==i and r['proof_sha256']==oldsvm['runs'][i]['proof_sha256'] and len(r['results'])==4
        for x in r['results']:
            assert x['heap_bytes']==262144 and x['unchanged_accounts']
            if x['cu_limit']==1000000:assert x['resource_failure'] and not x['custom_rejection'] and not x['accepted'] and x['cu']==1000000
            else:
                assert x['cu_limit']==100000000 and not x['resource_failure']
                if x['case']=='honest':assert x['accepted'];cu.append(x['cu'])
                else:assert x['case']=='bad-combined-final' and x['custom_rejection'] and not x['accepted'] and x['error']=='InstructionError(0, Custom(6))'
    reports[variant]={'cu':cu,'delta_vs_R61':[x-y for x,y in zip(cu,[1507423,1508805])],'logs':logs,'elf_sha256':svm['elf_sha256'],'selected':all(x<y for x,y in zip(cu,[1507423,1508805]))}
    if (d/'full-trace/analysis.json').exists():
        trace=json.loads((d/'full-trace/analysis.json').read_text());tr=json.loads((d/'full-trace/receipt.json').read_text())
        assert trace['elf_sha256']==tr['elf_sha256']==svm['elf_sha256']
        assert trace['exact_text_match'] and tr['clean_cu_equal'] and trace['cu']==tr['result']['cu']==cu[0]
        after=normal(trace);deltas={n:after.get(n,0)-before.get(n,0)for n in before.keys()|after.keys()if before.get(n,0)!=after.get(n,0)}
        assert sum(deltas.values())==trace['executed_instructions']-oldtrace['executed_instructions']==cu[0]-1507423
        if variant=='gather-checked':
            assert deltas=={'aspis_core::field::QM31::mul':-25883,'aspis_core::field::r25_checked_dot':26165,
                'aspis_v8_performance_sbf::r19_channel_ordinary::r62_gather':5819,
                'aspis_v8_performance_sbf::r19_channel_ordinary::terminal_scalar':-16147}
            assert trace['categories']['integer_multiply']==oldtrace['categories']['integer_multiply']==75158
            entries={re.sub(r'::h[0-9a-f]+$','',x['name']):x['entries']for x in trace['functions']}
            assert entries['aspis_core::field::r25_checked_dot']==84 and entries['aspis_core::field::QM31::mul']==1990
        reports[variant]['trace']={'resources':metrics(d/'full-trace/run.log'),'executed_instructions':trace['executed_instructions'],'exclusive_instruction_deltas':deltas}
assert reports['pair']['cu']==[1538501,1539654] and not reports['pair']['selected']
assert reports['gather-old']['cu']==[1534586,1536001] and not reports['gather-old']['selected']
assert reports['gather-checked']['cu']==[1497377,1498764] and reports['gather-checked']['selected']
records=json.loads((e/'lean/metadata.json').read_text());assert len(records)==296
for r in records:
    assert r['exit']==0 and r['toolchain']=='leanprover/lean4:v4.32.0'
    path=root/'lean'/(r['target_name']+'.lean');assert sha(path)==r['source_sha256'];pins[str(path.relative_to(repo))]=sha(path)
assert records[-1]['target_name']=='AspisV8R19/CorrectionGather' and records[-1]['base_revision']==base
lean=metrics(e/'lean/CorrectionGather.log');s=(e/'lean/CorrectionGather.log').read_text()
axioms=re.findall(r'depends on axioms: \[([^]]*)\]',s);assert len(axioms)==3 and all(x=='propext'for x in axioms)
assert 'sorryAx' not in s
receipt={'base_revision':base,'baseline_cu':[1507423,1508805],'source_pins_per_variant':197,'variants':reports,
    'resources':{'RustHigh':'5G','RustMax':'7G','runtimeHigh':'2G','runtimeMax':'3G','MemorySwapMax':0,'TasksMax':128,'max_simultaneous_reservation_gib':9},
    'actual_1M_gate_passed':False,'new_theorems':3,'Lean':lean,'final_cache_objects':296,'axioms_audits':3,
    'protocol_changed':False,'universal_Rust_refinement':False,'full_privacy':False,'full_soundness':False,'numerical_source_privacy_bound':None}
names=['stage_r62_ordinary.py','stage_r62_gather.py','r62_entry.rs','r62_gather.rs','run_r62_full.py','collect_r62_evidence.py','check_r62_evidence.py',
    'run_r62_lean.py','run_r50_lean.py','run_r23_full.py','build_r20_sbf.py','check_r19_wire_controls.py','run_r24_full_trace.py','analyze_r24_full_trace.py']
paths=[root/'tools'/n for n in names]+[parent/'r18-stage.json',parent/'r24-svm-a/receipt.json',parent/'full-trace/analysis.json',root/'lean/AspisV8R19/PartialDot.lean']
pins.update({str(f.relative_to(repo)):sha(f)for f in paths})
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');(e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    manifest={str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'}
    (e/'MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
assert json.loads((e/'receipt.json').read_text())==receipt and json.loads((e/'SOURCE_PINS.json').read_text())==pins
manifest=json.loads((e/'MANIFEST.json').read_text());assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h,n
print(json.dumps({'status':'PASS','artifacts':len(manifest),'variants':{n:{k:r[k]for k in ['cu','delta_vs_R61','selected']}for n,r in reports.items()},'actual_1M_gate_passed':False,'full_privacy':False},indent=2))
