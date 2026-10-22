from pathlib import Path
import json,subprocess,hashlib
E=Path(__file__).resolve().parent.parent
ROOT=Path.cwd(); frozen='6372708025a3dad1abf4addbb47a7a74b09b02be'
sha=lambda b:hashlib.sha256(b).hexdigest()
rows=[json.loads(l) for l in (E/'rust-receipts.jsonl').read_text().splitlines()]
accepted=[];lowerings=[];diagnostics=[]
for row in rows:
    name=row['name'];out=(E/'receipts'/name/'stdout.log').read_text()
    if 'kani' in row['command'] and row['exit_status']==0:
        assert 'VERIFICATION:- SUCCESSFUL' in out and '0 failures' in out,name
        accepted.append(name)
    elif name.endswith('-charon') and row['exit_status']==0:
        llbc=json.loads((E/(name[:-7]+'-llbc.json')).read_text())
        (lowerings if not llbc['has_errors'] else diagnostics).append(name)
    else:diagnostics.append(name)
    for path,want in row['source_hashes'].items():
        if path.startswith(('crates/','programs/')) and path not in ['crates/aspis-r1-cost-probe/src/sim.rs','crates/aspis-r1-cost-probe/src/sim_owned31.rs']:
            p=ROOT/path
            assert p.exists() and sha(p.read_bytes())==want,(name,path)
assert len(accepted)==5,accepted

def function(text,name):
    start=text.index('fn '+name+'(') if 'fn '+name+'(' in text else text.index('fn '+name+'<')
    begin=text.index('{',start);depth=0
    for i in range(begin,len(text)):
        if text[i]=='{':depth+=1
        if text[i]=='}':
            depth-=1
            if depth==0:return text[start:i+1]
    raise AssertionError(name)
final=Path('crates/aspis-r1-cost-probe/src/sim_owned31.rs').read_text()
checks={
    'publication31-wide_byte-v2':['wide_bytes'],
    'publication31-cell_transition-v2':['put_cell'],
    'publication31-capacity-oversized-v5':['append_nodes'],
    'publication31-capacity-exact-v5':['append_nodes'],
    'publication31-capacity-padded-v5':['append_nodes'],
}
helper_pins={}
for row in rows:
    if row['name'] not in checks:continue
    snapshots=row['source_snapshots']['sim_owned31.rs']
    tested=(E/snapshots[0]).read_text()
    for name in checks[row['name']]:
        assert function(final,name)==function(tested,name),(row['name'],name)
        helper_pins[name]=sha(function(final,name).encode())
# Native simulator source is unchanged; only a proof-config module declaration
# has been appended. The full reference has no equivalence certificate.
p='crates/aspis-r1-cost-probe/src/sim.rs'
base=subprocess.check_output(['git','show','b5e845cb4:'+p],text=True)
assert Path(p).read_text()==base+'\n#[cfg(any(kani,aeneas_ref))]\n#[path="sim_owned31.rs"]\npub mod owned31;\n'
elf=json.loads((E/'frozen-elf-final-check.json').read_text())
assert elf['source_revision']==frozen
for name,r in elf['programs'].items():
    assert r['byte_identical'] and r['cmp_exit']==0 and r['receipt']['exit_status']==0,name
inv=json.loads((E/'frozen-source-inventory.json').read_text())
assert inv['result']==dict(checked_files=493,differences=[])
for path,pin in inv['pins'].items():assert sha(Path(path).read_bytes())==pin['sha256'],path
endpoint=json.loads((E/'endpoint/identity.json').read_text())
assert endpoint['byte_identical'] and endpoint['premises_deleted']==0
result=dict(source_revision=frozen,accepted_bounded_kani=accepted,valid_charon_lowerings=lowerings,
    diagnostics=diagnostics,source_helper_sha256=helper_pins,shipped_inventory_files=493,
    frozen_elfs={name:{k:r[k] for k in ['sha256','size_bytes','cmp_exit','byte_identical']} for name,r in elf['programs'].items()},
    native_simulator_unchanged=True,publication_equivalence_certified=False,aeneas_owner_accepted=False,
    lean_attempts=[],new_theorems=[],print_axioms='N/A: no new Lean theorem or compilation',
    endpoint_identity=endpoint,target_established=False,
    trust_boundary='BTreeMap laws are retained TrustedStd facts; no successful raw-map Kani equivalence or cryptographic helper discharge is claimed.')
(E/'final-audit.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['source_revision','accepted_bounded_kani','valid_charon_lowerings','shipped_inventory_files','target_established']},indent=1))
