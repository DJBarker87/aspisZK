#!/usr/bin/env python3
"""L186 source-file pin census. Historical pins remain distinct from release inputs.
All requested packets are scanned, including failures; referenced JSON is followed.
Only the explicitly recorded, mechanically checked S4 delta can bridge a mismatch.
"""
import collections,hashlib,json,re,subprocess,sys,time,resource
from pathlib import Path
R=Path(__file__).resolve().parents[2]; E=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
sha=lambda p:H(p.read_bytes())
PREFIXES={'Op3I':'op3-install-20261025','Op4P':'op4-p6-20261025','Tx2I':'tx2-install-20261025','Op5T':'op5-tx2-20261025','SdkC':'sdk-child-20261025','SdkD':'sdk-child2-20261026','Tx1Q':'tx1-query-20261025','WAdm':'writer-adm-20261025','Tx2N':'tx2-inner-20261025','T2Nat':'tx2-native-20261026','CPhy':'compose-phys-20261026','AuS1':'auth-s1-20261026','GExp':'global-exp-20261026','GExq':'global-exp2-20261026','S2W/D189':'s2w-20261023'}
HEX=re.compile(r'^[a-f0-9]{64}$')

def norm(s):
    if not isinstance(s,str):return None
    for marker in ('crates/','programs/'):
        i=s.find(marker)
        if i>=0 and (i==0 or s[i-1]=='/'):return s[i:]
    if s in ('Cargo.lock','Cargo.toml'):return s
    if s.endswith('/src/Cargo.lock'):return 'Cargo.lock'
    return None

def bridge():
    delta=R/'evidence/s2w-20261023/d189-inherited-source-delta.json';d=json.loads(delta.read_text())
    p=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s4-zero-scanner-all-input-v1-20261023'
    extraction=p/'evidence/pair-zero-scanner-sdk-extraction-v5-stock-20261023'
    pins=json.loads((extraction/'input/source-pins.json').read_text());old,new=pins['cuts']
    a=(p/'rust-source/indexed-r1_pool_adapter_owned.rs').read_bytes();b=(R/d['source']).read_bytes()
    assert H(a)==old['source_sha256']==d['historical_sha256']
    assert H(b)==new['source_sha256']==d['current_sha256']
    ab=a[old['start_byte']:old['end_byte_exclusive']];bb=b[new['start_byte']:new['end_byte_exclusive']]
    assert H(ab)==old['body_sha256'] and H(bb)==new['body_sha256']
    assert ab.startswith(b'fn require_zero(') and bb.startswith(b'fn require_zero(')
    assert a[:old['start_byte']]+bb+a[old['end_byte_exclusive']:]==b
    # Check retained extraction kit, SDK nominal identities and generated adapter.
    gate=subprocess.run(['python3','-B',str(p/'check-source-pins.py')],cwd=R,capture_output=True,text=True)
    assert gate.returncode==0,gate.stderr
    theorem=R/d['helper_transport']['source'];assert sha(theorem)==d['helper_transport']['sha256']
    assert 'theorem all_input_source_equivalence' in theorem.read_text()
    audit=p/'evidence/a3-zero-scanner-all-input-equivalence-v3-check-20261023/evidence'
    rec=json.loads((audit/'receipt.json').read_text());assert rec['exit_status']==0 and rec['source_sha256']==sha(theorem)
    log=(audit/'lean.log').read_text();m=re.search("'"+re.escape(d['helper_transport']['theorem'])+r"' depends on axioms: \[([^]]*)\]",log,re.S)
    assert m and set(m[1].replace('\n',' ').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}
    packet=json.loads((p/'proof-packet.json').read_text())
    assert packet['source_pins']=={'indexed_full_file':H(a),'tail_full_file':H(b),'indexed_body':H(ab),'tail_body':H(bb)}
    for name,check in packet['accepted_focused_checks'].items():
        f=p/'sources'/(name.replace('.','/')+'.lean')
        assert sha(f)==check['source_sha256'] and check['exit_status']==0
    assert sha(theorem) in json.dumps(packet) and 'ZeroScannerSourceStepsV1' in theorem.read_text()
    return {'delta':str(delta.relative_to(R)),'delta_sha256':sha(delta),'source':d['source'],'old_sha256':H(a),'new_sha256':H(b),'old_body_sha256':H(ab),'new_body_sha256':H(bb),'replacement_byte_identical':True,'theorem':d['helper_transport']['theorem'],'theorem_source_sha256':sha(theorem),'audit_receipt':str((audit/'receipt.json').relative_to(R)),'audit_receipt_sha256':sha(audit/'receipt.json'),'axioms_line':m[0],'source_pin_checker_stdout':gate.stdout,'source_pin_checker_sha256':sha(p/'check-source-pins.py'),'extraction_source_pins_sha256':sha(extraction/'input/source-pins.json')}

def main():
    started=time.monotonic();errors=[]
    try:br=bridge()
    except (AssertionError,KeyError,FileNotFoundError) as ex:br=None;errors.append({'bridge_error':str(ex)})
    roots={k:R/'evidence'/v for k,v in PREFIXES.items()}
    queue=set(q for p in roots.values() for q in p.rglob('*.json'))
    checked={};rows=[];nonrelease=[]
    def add(evidence,pointer,raw,expected):
        if not isinstance(expected,str) or not HEX.fullmatch(expected):return
        n=norm(raw)
        if not n:
            if isinstance(raw,str) and (raw.endswith('.rs') or raw.endswith('Cargo.toml')):
                nonrelease.append({'evidence':str(evidence.relative_to(R)),'pointer':pointer,'raw_source':raw,'expected_sha256':expected})
            return
        # Source code, manifests, lockfile only; no proof/generated artifact hashes.
        if not (n.endswith('.rs') or n.endswith('Cargo.toml') or n=='Cargo.lock'):return
        cur=R/n;actual=sha(cur) if cur.is_file() else None
        status='match' if actual==expected else 'mismatch'
        if br and n==br['source'] and expected==br['old_sha256'] and actual==br['new_sha256']:status='bridged'
        rows.append({'evidence':str(evidence.relative_to(R)),'pointer':pointer,'raw_source':raw,'source':n,'expected_sha256':expected,'release_sha256':actual,'status':status})
    def walk(x,evidence,pointer=''):
        if isinstance(x,dict):
            for k,v in x.items():
                pp=pointer+'/'+k.replace('~','~0').replace('/','~1')
                if isinstance(v,str):add(evidence,pp,k,v)
                elif isinstance(v,dict):
                    for hk in ('sha256','source_sha256','expected'):
                        if hk in v:add(evidence,pp+'/'+hk,k,v[hk])
                walk(v,evidence,pp)
            for pk,hks in [('path',('sha256','source_sha256','expected')),('source',('source_sha256','sha256','historical_sha256','current_sha256')),('native_source',('native_sha256',))]:
                if isinstance(x.get(pk),str):
                    for hk in hks:
                        if hk in x:add(evidence,pointer+'/'+hk,x[pk],x[hk])
        elif isinstance(x,list):
            for i,v in enumerate(x):walk(v,evidence,pointer+'/'+str(i))
        elif isinstance(x,str):
            # Follow explicit repository JSON associations, not arbitrary host paths.
            p=R/x
            if len(x)<512 and '\n' not in x and x.endswith('.json') and not x.startswith('/'):
                if p.is_file() and p not in checked:queue.add(p)
    while queue:
        p=min(queue);queue.remove(p)
        if p in checked:continue
        try:data=json.loads(p.read_text())
        except (ValueError,UnicodeError) as ex:errors.append({'evidence':str(p.relative_to(R)),'parse_error':str(ex)});continue
        checked[p]=sha(p);walk(data,p)
    # Deduplicate exact evidence locations; retain every historical expected value.
    rows=list({(r['evidence'],r['pointer'],r['source'],r['expected_sha256']):r for r in rows}.values())
    rows.sort(key=lambda r:(r['source'],r['expected_sha256'],r['evidence'],r['pointer']))
    build=json.loads((E/'Low2_build_inputs.json').read_text())
    for r in rows:
        r['build_input_sha256']=build['files'].get(r['source'])
        if r['release_sha256']!=r['build_input_sha256']:r['status']='missing_or_changed_build_input'
    # Verification kit/reference files are not release compilation units. Retain
    # their exact hash identities separately; external SDK inputs are audited
    # against the compiler registry by the build-host collector.
    tracked=subprocess.check_output(['git','ls-files','-z'],cwd=R).decode().split('\0')
    byname=collections.defaultdict(list)
    for f in tracked:
        if f.endswith(('.rs','Cargo.toml')):byname[Path(f).name].append(f)
    cache={}; snapshots=[]
    for r in nonrelease:
        key=(r['raw_source'],r['expected_sha256'])
        if key not in cache:
            direct=R/r['raw_source']
            candidates=([str(direct.relative_to(R))] if direct.is_relative_to(R) and direct.is_file() else [])+byname[Path(r['raw_source']).name]
            matches=[f for f in dict.fromkeys(candidates) if sha(R/f)==r['expected_sha256']]
            cache[key]=matches
        r['retained_exact_files']=cache[key]
        r['classification']='verification_snapshot_identity' if cache[key] else 'external_or_unretained_source'
        snapshots.append(r)
    counts=dict(collections.Counter(r['status'] for r in rows))
    out={'row':'L186','source_revision':build['source_revision'],'audit_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'packet_roots':{k:str(v.relative_to(R)) for k,v in roots.items()},'evidence_files':[{'path':str(p.relative_to(R)),'sha256':s} for p,s in sorted(checked.items())],'bridge':br,'checks':rows,'verification_source_pins':snapshots,'verification_source_counts':dict(collections.Counter(r['classification'] for r in snapshots)),'counts':counts,'errors':errors,'scope':'All whole release-source file pins in JSON of requested packets and recursively referenced repository JSON. Kit/harness/Lean/body hashes are not whole release-source pins. Compilation membership is checked separately against compiler depfiles.','complete_source_to_elf_link':False}
    (E/'Low2_source_pin_check.json').write_text(json.dumps(out,indent=2)+'\n')
    exitcode=int(bool(errors or any(r['status'] not in ('match','bridged') for r in rows)))
    usage=resource.getrusage(resource.RUSAGE_SELF)
    receipt={'target':'Low2 whole-source identity census + S4 exact replacement bridge','command':['python3','-B','evidence/lowering2-20261026/Low2_check_source_pins.py'],'source_revision':out['source_revision'],'checker_sha256':sha(Path(__file__)),'deps_fingerprint':H(json.dumps(out['evidence_files'],sort_keys=True).encode()),'exit_status':exitcode,'wall_seconds':time.monotonic()-started,'peak_rss_bytes':usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,'swaps':usage.ru_nswap,'print_axioms':'No new theorem. S4 reused exact audit is embedded in bridge.','counts':counts}
    (E/'Low2_source_pin_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps({'counts':counts,'errors':errors,'evidence_files':len(checked),'unique_source_pins':len({(r['source'],r['expected_sha256']) for r in rows})}))
    return exitcode
if __name__=='__main__':sys.exit(main())
