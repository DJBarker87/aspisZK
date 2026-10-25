"""Local source/evidence finalization; immutable Git beforeimages only."""
import ast,difflib,hashlib,json,subprocess
from pathlib import Path
E=Path(__file__).resolve().parent
ROOT=E.parents[2]
D=ROOT/'tools/prover-rw-20261023/final-native-gate'
BASE='e8ffe0b688735e46e397c7aa0c0b2e8aa3c68b7e'
PREFIX='tools/prover-rw-20261023/final-native-gate/'

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def write(name,value):
    with (E/name).open('x') as f:json.dump(value,f,sort_keys=True,indent=2);f.write('\n')
def definitions(raw):
    return {n.name:ast.get_source_segment(raw.decode(),n) for n in ast.parse(raw).body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef,ast.ClassDef))}


def main():
    manifest={};before_manifest={};changes={};diff=[]
    for path in sorted(D.iterdir()):
        if not path.is_file():continue
        after=path.read_bytes();manifest[path.name]=pin(after)
        result=subprocess.run(['git','show',BASE+':'+PREFIX+path.name],cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        before=result.stdout if result.returncode==0 else b''
        if result.returncode==0:before_manifest[path.name]=pin(before)
        if before==after:continue
        row=dict(before_pin=pin(before) if result.returncode==0 else None,after_pin=pin(after))
        if path.suffix=='.py':
            a,b=definitions(before),definitions(after)
            row['complete_changed_functions_and_classes']={k:dict(before=a.get(k),after=b.get(k)) for k in sorted(set(a)|set(b)) if a.get(k)!=b.get(k)}
        changes[path.name]=row
        diff.extend(difflib.unified_diff(before.decode().splitlines(True),after.decode().splitlines(True),fromfile=BASE+'/'+path.name,tofile='source020/'+path.name))
    write('FinalNativeGate-source-manifest-020.json',manifest)
    write('FinalNativeGate-before-manifest-020.json',before_manifest)
    write('FinalNativeGate-source-functions-020.json',dict(base=BASE,changes=changes,
        security_premise_changes='N/A: no theorem/security premises altered. Operational reporting adds explicit same-execution not_started plus absent handles. All uncertain/owned paths retain real control protocol.',print_axioms='N/A'))
    with (E/'FinalNativeGate-source-diff-020.txt').open('x') as f:f.write(''.join(diff))
    historical={}
    for version in range(1,5):
        name='prospective-data-v'+str(version)
        args=['git','diff','--exit-code',BASE,'--',PREFIX+name]
        p=subprocess.run(args,cwd=ROOT,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        assert p.returncode==0,(name,p.stdout,p.stderr)
        historical[name]=dict(command=args,exit=p.returncode,
            git_tree=subprocess.check_output(['git','rev-parse',BASE+':'+PREFIX+name],cwd=ROOT,text=True).strip())
    # Preserve original report/query/diagnostic artifacts: only explicit source
    # migration/compact/lifecycle files and new v5 artifacts may differ.
    initial=json.loads((E/'FinalNativeGate-v5-superseded-019.json').read_bytes())
    prior=Path(initial['retained_release'])
    assert (prior/'payload/FinalNativeGate_compact.py').read_bytes()==(D/'FinalNativeGate_compact.py').read_bytes()
    first=definitions((prior/'payload/FinalNativeGate-transfer-template.txt').read_bytes())
    final=definitions((D/'FinalNativeGate-transfer-template.txt').read_bytes())
    assert first==final,'receiver semantic functions changed since extra019 fixtures'
    release=json.loads((D/'prospective-data-v5/FinalNativeGate-release-identities.json').read_bytes())
    reproduction=json.loads((E/'FinalNativeGate-v5-reproduction-020.json').read_bytes())
    results=[]
    for path in sorted(E.glob('v5-*-020.json')):
        r=json.loads(path.read_bytes())
        if 'target' in r:results.append({k:r[k] for k in ('target','argv','exit','wall_seconds','peak_rss_bytes','swap','source_revision','print_axioms')})
    extra_source=E/'v5-extra-fixtures-019.py'
    write('FinalNativeGate-v5-summary-020.json',dict(base=BASE,
        source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),source_manifest=manifest,
        exact_claim='Focused source fixtures establish future bounded semantic projection, truthful no-start reporting, preserved owned/uncertain cleanup paths, private publication and exact new v5 root/receiver behavior in mocks; final prospective source release reproduces byte-identically.',
        before_after='Full source-functions-020.json and source-diff-020.txt; operational statements in FinalNativeGate-V5-REVIEW-019.md with final correction in REVIEW-020.md; no historical-v4 byte identity claim.',
        source_seals={n:manifest[n] for n in ('FinalNativeGate-plan.json','FinalNativeGate_seal.py','FinalNativeGate-bootstrap.json','FinalNativeGate_bootstrap_seal.py')},
        release={k:release[k] for k in ('receiver','transport','transfer_manifest_root','transfer_manifest','source_manifest','changed_files','entry_deltas','unchanged_policy_bundles')},
        byte_identical_reproduction=reproduction['byte_identical'],reproduction=pin((E/'FinalNativeGate-v5-reproduction-020.json').read_bytes()),
        results=results,finalizer_source=pin(Path(__file__).read_bytes()),
        superseded='Source019/v5 first candidate retained in v5-superseded-019.json; project exception ordering corrected in source020. Earlier fixture failures019a/b retained, no resource failure or cap increase.',
        focused_tests=dict(new_source020=23,new_release020=19,reused_extra019=2,
            reused_extra_source=dict(path=extra_source.name,**pin(extra_source.read_bytes())),
            reused_extra_receipt=pin((E/'v5-extra-fixtures-019.json').read_bytes()),
            reuse_assessment='compact source bytes and complete receiver semantic functions identical to first019 candidate; only embedded final payload/pins differ, verified by final020 release fixtures; no host evidence promotion'),
        old_report=dict(reason='UNKNOWN',prior_query_exit=78,prior_stat_size=14107502,bytes_read=0,complete_hash=None,decision_data=None,authority='manager-supplied historical observation; not revalidated'),
        historical_releases_unchanged=historical,
        assumptions=dict(discharged=[],added=[],changed=[],retained=['Python/stdlib/OS operational observations','all SDK/std/runtime/allocator/extraction/sourceDrop/child/mark/P2Prime/native/artifact/security joins','future host visibility/environment/bus/control permissions/stage absence remain unobserved']),
        actual_host_actions=dict(total=0,SSH=0,upload=0,setup=0,query=0,Lean=0,Kani=0,Cargo=0,Rust=0,compiler=0,native_backend=0,ELF_rebuild=0,permission_changes=0,key_actions=0,RPC=0),
        local_permission_fixtures='Private fresh test files only; temporary umask002/777 restored; no existing chmod/chown or host permission change. This qualifies the host-only zero permission count in superseded019 summary.',
        print_axioms='N/A: Python source fixtures and text/AST audit; no formal theorem/import',targets_established=False,no_final_charge_authority=True,
        next='Lead source020/v5 review, then ONE separately allocated future v5 DATA action only; STOP now'))
    print(json.dumps(dict(changed_files=len(changes),receiver=release['receiver'],transport=release['transport'],transfer_root=release['transfer_manifest_root'],source_manifest=pin((E/'FinalNativeGate-source-manifest-020.json').read_bytes()),print_axioms='N/A',host_actions=0)))

if __name__=='__main__':main()
