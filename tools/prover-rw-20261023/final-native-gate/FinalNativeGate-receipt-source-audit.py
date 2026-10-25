"""Focused AST/import/pin audit only; no producer, release refresh or host action."""
import ast, hashlib, json, subprocess
from pathlib import Path
D=Path(__file__).resolve().parent;ROOT=D.parents[2]
E=ROOT/'evidence/prover-rw-20261023/final-native-gate';BEFORE=E/'FinalNativeGate-maintained-before-010'
BASE='b5b4339499'
def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())
def write(name,value):
    with (E/name).open('x') as f:json.dump(value,f,sort_keys=True,indent=2);f.write('\n')
def functions(raw):
    source=raw.decode()
    return {n.name:ast.get_source_segment(source,n) for n in ast.parse(source).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
def main():
    manifest={p.name:pin(p.read_bytes()) for p in sorted(D.iterdir()) if p.is_file()}
    changed={}
    for p in sorted(BEFORE.iterdir()):
        after=(D/p.name).read_bytes();before=p.read_bytes()
        if after==before:continue
        a,b=functions(before),functions(after)
        changed[p.name]=dict(before_pin=pin(before),after_pin=pin(after),complete_changed_functions={k:dict(before=a.get(k),after=b.get(k)) for k in sorted(set(a)|set(b)) if a.get(k)!=b.get(k)})
    assert set(changed)=={'FinalNativeGate_setup.py'},set(changed)
    assert set(changed['FinalNativeGate_setup.py']['complete_changed_functions'])=={'_publish'}
    write('FinalNativeGate-source-functions-011.json',dict(base=BASE,changes=changed,theorem_premise_changes='N/A: no theorem changes',claim='Private filesystem publication only; no output/security equivalence theorem'))
    imports={}
    for name in manifest:
        if not name.endswith('.py'):continue
        tree=ast.parse((D/name).read_bytes());imports[name]=[]
        for node in ast.walk(tree):
            if isinstance(node,ast.Import):imports[name].extend(a.name for a in node.names)
            if isinstance(node,ast.ImportFrom):imports[name].append(node.module)
    for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py','FinalNativeGate-receipt-diagnostic.py','FinalNativeGate-receipt-transport.py'):
        main=functions((D/name).read_bytes())['main'];tree=ast.parse(main)
        assert any(isinstance(n,ast.Return) and isinstance(n.value,ast.Constant) and n.value.value==78 for n in ast.walk(tree))
        assert not any(isinstance(n,ast.Call) and isinstance(n.func,ast.Name) and n.func.id in ('_collect','_prospective','_bound_body','_reviewed_future','diagnostic_entry') for n in ast.walk(tree))
    diag=(D/'FinalNativeGate-receipt-diagnostic.py').read_bytes()
    payload=(D/'FinalNativeGate-receipt-diagnostic-payload.txt').read_bytes()
    assert payload==diag.replace(b"if __name__=='__main__':raise SystemExit(main())",b"if __name__=='__main__':raise SystemExit(diagnostic_entry())")
    tree=ast.parse((D/'FinalNativeGate-receipt-transport.py').read_bytes())
    values={node.targets[0].id:ast.literal_eval(node.value) for node in tree.body if isinstance(node,ast.Assign) and isinstance(node.targets[0],ast.Name) and node.targets[0].id in ('PIN','ARGV')}
    assert values['PIN']==pin(payload)
    assert set(imports['FinalNativeGate-receipt-diagnostic.py'])=={'hashlib','json','math','os','signal','stat'}
    # Frozen release and old evidence are compared by Git path/object identity;
    # never read old host action logs or a live cache, and never replay v4.
    touched=subprocess.check_output(['git','diff','--name-only',BASE,'--'],cwd=ROOT,text=True).splitlines()
    allowed_prefixes=('tools/prover-rw-20261023/final-native-gate/','evidence/prover-rw-20261023/final-native-gate/')
    assert all(p.startswith(allowed_prefixes) for p in touched)
    assert not any('/prospective-data-' in p for p in touched)
    assert not any(p.startswith(('crates/','programs/')) for p in touched)
    write('FinalNativeGate-receipt-seals-011.json',dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        maintained_source_status='UNSEALED / NOT READY; historical plan/bootstrap seals intentionally stale',
        manifest=manifest,diagnostic_payload=pin(payload),transport=pin((D/'FinalNativeGate-receipt-transport.py').read_bytes()),
        future_argv=values['ARGV'],future_capture='/private/tmp/FinalNativeGate-receipt-diagnostic-010-future',
        imports=imports,operational_mains_disabled=True,frozen_v4_paths_changed=False,
        actual_SSH=0,host_actions=0,setup=0,compiler=0,Lean=0,Kani=0,security_targets_established=False,
        source_claim='Mode0600 exclusive private publication; bounded untrusted read-only diagnostic proposal',
        original_receiver_predicate='regular and nlink1 and currentUID and (mode & 0o022)==0; unchanged',
        assumptions_added=[],formal_assumptions_discharged=[],
        retained_boundaries=['Python/stdlib/OS operational behavior','all existing prospective/inside/GO/reservation/guard/rawvisibility/control/order/cleanup/handshake/descriptor/security predicates'],
        reused_validation='Manager-provided actualv4 observation only; immutable v4 source provenance; no new remote identity gate',
        remaining_blocker='Actual diagnostic error/current mode/host umask UNOBSERVED; lead review then explicit allocation before any SSH',
        print_axioms='N/A: source/AST/import audit; no Lean or formal theorem'))
    diff=subprocess.check_output(['git','diff',BASE,'--','tools/prover-rw-20261023/final-native-gate/FinalNativeGate_setup.py'],cwd=ROOT)
    with (E/'FinalNativeGate-source-publication-diff-011.txt').open('xb') as f:f.write(diff)
    print(json.dumps(dict(changed_functions=['FinalNativeGate_setup._publish'],diagnostic_payload=pin(payload),transport=pin((D/'FinalNativeGate-receipt-transport.py').read_bytes()),actual_SSH=0,print_axioms='N/A')))
if __name__=='__main__':main()
