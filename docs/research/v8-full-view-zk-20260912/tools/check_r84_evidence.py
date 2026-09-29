#!/usr/bin/env python3
"""Audit failed original candidate, repaired finite gates and NEW-profile CU."""
import argparse,ast,hashlib,json,re,subprocess,sys
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--record',action='store_true');a=p.parse_args()
root=Path(__file__).resolve().parent.parent;repo=root.parents[2];e=root/'evidence/r84-bitperm'
subprocess.run([sys.executable,str(root/'tools/check_r83_evidence.py')],stdout=subprocess.DEVNULL,check=True)
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
def j(f):return json.loads(f.read_text())
def blob(h):
    f=e/'blobs'/h;assert sha(f)==h;return f
def metrics(f):
    s=f.read_text();t=re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([\d:.]+)',s)[1]
    return {'exit':int(re.search(r'Exit status: (\d+)',s)[1]),'swaps':int(re.search(r'Swaps: (\d+)',s)[1]),
        'wall_s':round(sum(float(x)*60**i for i,x in enumerate(reversed(t.split(':')))),2),
        'peak_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',s)[1])}
pm=j(e/'control/r18-stage.json');assert sha(e/'control/r18-stage.json')=='f70d74f4e479899b7eda0664a4dfdf4b8e8068d7bf9be836a2cd681397167498'
original=j(e/'control/sources.json')
for n,h in original.items():
    if n in pm['files']:assert h==pm['files'][n]
    blob(h)
reports={};ex='docs/research/v8-no-work-100-20260907/experiments/'
for variant in ['one-swap-initial','one-swap-dependency','two-swap-affine','compact']:
    d=e/variant;m=j(d/'r18-stage.json');sources=j(d/'sources.json');arts=j(d/'artifacts.json')
    def art(n):return blob(arts[n])
    assert len(m['files'])==212 and set(pm['files'])<=set(m['files'])
    assert sources=={n:h for n,h in m['files'].items()if pm['files'].get(n)!=h}
    allowed={ex+n for n in ['r16_basis_transport.rs','r17_basis_tables.rs','performance_verifier.rs','payment_extraction.rs',
        'r17_host_relation.rs','r17_c1_witness_audit.rs','performance.rs','r84_bitperm_check.rs',
        'performance-host/Cargo.toml','performance-sbf/Cargo.toml']}
    if variant=='compact':allowed|={ex+n for n in ['query_arithmetic.rs','r55_opening_check.rs','r19_channel_ordinary.rs','r22_scalar.rs']}
    assert set(sources)==allowed
    for n,h in sources.items():blob(h)
    table=blob(sources[ex+'r17_basis_tables.rs']).read_text()
    order=ast.literal_eval(re.search(r'ORDER: \[usize; 1024\] = (\[[^;]+\]);',table)[1])
    candidate=[(x&1)|(((x>>1)&63)<<4)|(((x>>7)^7)<<1)for x in range(1024)]
    candidate[127],candidate[1023]=candidate[1023],candidate[127]
    two=variant in ['two-swap-affine','compact']
    if two:candidate[126],candidate[1021]=candidate[1021],candidate[126]
    assert order==candidate and sorted(order)==list(range(1024)) and order[1023]==1023
    assert order[:89]==[16*(x//2)+14+x%2 for x in range(89)]
    # No chronology or hashing change hidden in the new profile adapter.
    old=blob(original[ex+'r17_host_relation.rs']).read_text()
    old=old.replace('AV8/R19/compact-functional/sparseG-T163/channel-fold/v1',
        'AV8/R84/functional/'+('sparseG-bitperm-two-swaps/channel-fold/v2'if two else'sparseG-bitperm-swap/channel-fold/v1'))
    old=old.replace('AV8/R19/four-image-residuals/pre-channel/v1','AV8/R84/four-image-residuals/pre-channel/'+('v2'if two else'v1'))
    assert old==blob(sources[ex+'r17_host_relation.rs']).read_text()
    audit=blob(sources[ex+'r17_c1_witness_audit.rs']).read_text()
    assert 'assert_eq!(pivots.len(),540);' in audit and 'affine H1 joint compatibility' in audit
    assert 'original G row {i}' in audit and 'affine G witness compatibility' in audit
    logs={n:metrics(blob(h))for n,h in arts.items()if n.endswith('.log')}
    assert all(v['swaps']==0 for v in logs.values())
    for n,h in arts.items():
        if n.endswith('/resources.json'):
            r=j(blob(h));hi,ma=(12,16)if n.startswith('r24-sbf')else(2,3)if n.startswith('r24-svm')else(5,7)
            assert [r[k]for k in ['memory.high','memory.max','memory.swap.max','pids.max']]==[str(hi*2**30),str(ma*2**30),'0','128']
    leaf='r24-host-a/compact-check.log'if variant=='compact'else'r84-leaf/check.log'
    t=art(leaf).read_text()
    assert 'all_column_legal_pads=89' in t and 'inverse_basis_cases=1024' in t and 'tensor_coefficients=65536' in t and 'full_dual_chord_image_final_cases=64' in t
    assert logs[leaf]['exit']==0
    prefix_results={}
    if variant!='compact':
        for w in ([0]if variant=='one-swap-initial'else[0,1]):
            name=f'r84-prefix-world{w}/prefix.log';t=art(name).read_text()
            assert 'R17_C1_WITNESS_CORRECTION columns=16 rank_per_column=108' in t
            if not two:
                assert 'rank=539 expected_rank=540' in t and 'affine_nonzero_residuals=0' in t
                assert logs[name]['exit']==101 and 'R84_FULL_AFFINE_PREFLIGHT_PASS' not in t
                if variant=='one-swap-dependency':
                    assert 'active_balance_final_rows=471 rank=470 dependencies=1' in t
                    assert 'original_columns_checked=1022 source_target_zero=true' in t
                    for label in ['active:993','active:1008','balance','final:255']:assert label in t
            else:
                assert logs[name]['exit']==0
                for marker in ['active_balance_final_rows=471 rank=471 dependencies=0','rank=540 expected_rank=540','R19_G_WITNESS_JOINT equations=626 rank=602','R19_CHANNEL_WITNESS source_p0_p2_retained=true first_relation_all7=true combined_final256=true decoder_independent=true','R17_C1_WITNESS_VALIDATED same_public=true','R84_FULL_AFFINE_PREFLIGHT_PASS']:
                    assert marker in t,marker
            prefix_results[str(w)]={'exit':logs[name]['exit'],'H1_rank':540 if two else 539,'affine_target_compatible':True}
    else:
        assert m['basis_profile']=='signed-bit-permutation-two-swaps' and not m['r84_compact']['security_promoted']
        assert m['r84_compact']['input_manifest_sha256']==sha(e/'two-swap-affine/r18-stage.json')
        affine=j(e/'two-swap-affine/artifacts.json')
        assert m['r84_compact']['affine_gate_logs']=={str(w):affine[f'r84-prefix-world{w}/prefix.log']for w in range(2)}
        native=root/'evidence/r83-native/packed-block'
        assert m['r84_compact']['native_manifest_sha256']==sha(native/'r18-stage.json')
        native_source=j(native/'sources.json')
        for n in ['query_arithmetic.rs','r55_opening_check.rs']:assert sources[ex+n]==native_source[ex+n]
        assert all(v['exit']==0 for v in logs.values())
        for w in range(2):assert 'R17_PUBLIC_PREFIX_ACCEPTED' in art(f'r24-host-a/world{w}.log').read_text()
        wire=j(art('wire-controls.json'));assert len(wire['cases'])==3282 and all(x['exit']==0 for x in wire['cases'])
        assert sum(x['checked_rejection']for x in wire['cases'])==3281
        assert 'compact_source_implemented=true' in art(leaf).read_text()
        build=art('r24-sbf-a/compile.log').read_text()
        assert 'overflows the maximum allowed frame'not in build and not('Stack offset'in build and 'exceeded'in build)
        assert 'all 1024 source permutation and inactive entries match SBF table'in build
        svm=j(art('r24-svm-a/receipt.json'));assert svm['full_verifier'] and svm['new_profile'] and not svm['security_promoted']
        na=j(native/'artifacts.json');ns=j(root/'evidence/r83-native/blobs'/na['r24-svm-a/receipt.json'])
        assert svm['driver_sha256']==ns['driver_sha256']
        assert svm['source_manifest_sha256']==sha(d/'r18-stage.json')
        assert svm['elf_sha256']==j(art('r24-sbf-a/environment.json'))['elf_sha256']
        cu=[];passes=[]
        assert len({r['proof_sha256']for r in svm['runs']})==2
        for w,r in enumerate(svm['runs']):
            assert r['world']==w and len(r['results'])==4
            for x in r['results']:
                assert x['unchanged_accounts'] and x['heap_bytes']==262144
                if x['case']=='honest':
                    if x['cu_limit']==100000000:assert x['accepted'] and not x['resource_failure'];cu.append(x['cu'])
                    else:
                        assert x['cu_limit']==1000000
                        if not x['accepted']:assert x['resource_failure'] and x['cu']==1000000 and not x['custom_rejection']
                        passes.append(x['accepted'])
                else:
                    assert not x['accepted']
                    if x['cu_limit']==100000000:assert x['custom_rejection'] and not x['resource_failure']
        prefix_results={'cu':cu,'actual_1M_passes':passes,'elf_sha256':svm['elf_sha256']}
    reports[variant]={'metrics':logs,'result':prefix_results}
receipt={'variants':reports,'security_promoted':False,'new_profile':True,'new_Lean_targets':0,'full_privacy':False,'full_soundness':False,
    'selected_unchanged_profile_cu':[1326977,1328177],
    'first_security_obligation':'Universal actual-source C1/H1/G affine image compatibility for the two-swap map, including channel messages and degenerate/adaptive prefixes; finite screens are insufficient.'}
paths=[root/'tools'/n for n in ['stage_r84_bitperm.py','r84_bitperm_check.rs','r84_h1_dependency.rs','run_r84_gate.py','stage_r84_compact.py','r84_compact.rs','build_r84_sbf.py','run_r84_full.py','collect_r84_evidence.py','check_r84_evidence.py']]
paths += [root/'evidence/r83-native/MANIFEST.json',root/'r18-pack/evidence/NEGATIVE_RESULTS.md']
pins={str(f.relative_to(repo)):sha(f)for f in paths}
if a.record:
    (e/'receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    (e/'SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
    (e/'MANIFEST.json').write_text(json.dumps({str(f.relative_to(e)):sha(f)for f in sorted(e.rglob('*'))if f.is_file()and f.name!='MANIFEST.json'},indent=2)+'\n')
assert j(e/'receipt.json')==receipt and j(e/'SOURCE_PINS.json')==pins
manifest=j(e/'MANIFEST.json');assert set(manifest)=={str(f.relative_to(e))for f in e.rglob('*')if f.is_file()and f.name!='MANIFEST.json'}
for n,h in manifest.items():assert sha(e/n)==h
print(json.dumps({'status':'PASS','compact':reports['compact']['result'],'security_promoted':False,'artifacts':len(manifest)}))
