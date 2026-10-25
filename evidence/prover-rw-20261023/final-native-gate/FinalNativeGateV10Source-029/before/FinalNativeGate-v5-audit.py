"""Focused local AST/text/pin audit only. Does not execute release entries."""
import ast,hashlib,json
from pathlib import Path
D=Path(__file__).resolve().parent
E=D.parents[2]/'evidence/prover-rw-20261023/final-native-gate'
BASE=E/'v5-beforeimages-019'
STAGE='/home/dombarker/final-native-gate-v5-20261025'

def main():
    for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
        raw=(D/name).read_text();tree=ast.parse(raw)
        main=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='main')
        assert len(main.body)==2 and main.body[-1].value.value==78,name
        assert STAGE in raw
    for name in ('FinalNativeGate_reviewed.json','FinalNativeGate_policy.py','FinalNativeGate_setup_adapter.py'):
        assert (D/name).read_bytes()==(BASE/name).read_bytes(),name
    before=(BASE/'FinalNativeGate_scope.py').read_text().replace('/home/dombarker/final-native-gate',STAGE)
    assert (D/'FinalNativeGate_scope.py').read_text()==before,'FixedScope semantic change'
    plan=json.loads((D/'FinalNativeGate-plan.json').read_bytes())
    for key in ('catalogs','environment','host_runtime','inherited_limits','cache_inventory','cache_output_bounds','native_runtime_dependencies'):
        assert key in plan and plan[key] is None,key
    text=(D/'FinalNativeGate-transfer-template.txt').read_text()
    assert text.count("'final-native-gate-v5-20261025'")==3
    assert "if STAGE!="+repr(STAGE) in text
    assert "os.mkdir('final-native-gate'," not in text
    assert "names=('FinalNativeGate-setup-terminal.json','FinalNativeGate-setup-parent-terminal.json'," in text
    assert "public=set(names[:3])" in text
    # Exact finite source roots, not a source-to-executed-code identity theorem.
    bootstrap=json.loads((D/'FinalNativeGate-bootstrap.json').read_bytes())
    for name,pin in bootstrap.items():
        raw=(D/name).read_bytes()
        assert dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())==pin,name
    assert (D/'FinalNativeGate_seal.py').read_text()=='PLAN_SHA256 = '+repr(hashlib.sha256((D/'FinalNativeGate-plan.json').read_bytes()).hexdigest())+'\n'
    assert (D/'FinalNativeGate_bootstrap_seal.py').read_text()=='BOOTSTRAP_SHA256 = '+repr(hashlib.sha256((D/'FinalNativeGate-bootstrap.json').read_bytes()).hexdigest())+'\n'
    print(json.dumps(dict(source_only=True,public_summary_files=5,new_stage=STAGE,policy_unchanged=True,seven_fresh_fields_null=True,print_axioms='N/A',host_actions=0)))

if __name__=='__main__':main()
