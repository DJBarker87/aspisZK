"""Read-only boundary inventory: no prover or build is launched."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]; D=R/'docs/research/100bit-spend-path-20261013'; E=D/'evidence/s2x-20261023'
def pin(p):
 b=p.read_bytes();return dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
p=D/'lean/AdapterRwModel.lean';s=p.read_text();body=s.split('structure Ops where\n',1)[1].split('\n\n',1)[0]
ops=re.findall(r'^  op(\d+) : (.*?)(?=\n  op\d+ :|\Z)',body,re.M|re.S)
assert [int(n) for n,_ in ops]==list(range(54))
groups={**{i:'comparison/range/option' for i in range(10)},10:'TX1 verifier',11:'TX2 verifier',12:'checkpoint sizing',**{i:'statement/registry/tag/lane' for i in range(13,35)},35:'ProgramError clone',36:'Pubkey equality',37:'Pubkey from array',38:'PDA creation',39:'Pubkey bytes',40:'Pubkey slice',41:'Pool ID',42:'SolanaDigest copy',43:'SHA digest',44:'verifier error mapping',45:'profile constant',46:'release constant',47:'public decoder',48:'master decoder',49:'Pool checkpoint decoder',50:'lane decoder',51:'proof scanner',52:'statement reconstruction',53:'result emission'}
x=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),extraction=pin(p),operations=[dict(name='op'+n,kind=groups[int(n)],type=' '.join(t.split())) for n,t in ops],sdk_snapshot_operations_in_ops=0,sdk_write_operations_in_ops=0,wrapper=pin(R/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'),extracted_types=pin(D/'lean/AdapterRwTypes.lean'),runtime_admission=pin(D/'lean/AdapterRwRuntimeAdmission.lean'),trusted_sdk=pin(D/'lean/S2TrustedSdkBorrow.lean'),release_pins={'default':'d7d42f770883401e0104fb6e044f61a132fea7359943db225d581c5740fcffd0','devnet':'2b2a9f0e7a2f93004ddbf207d02f5c5d5155d5c9bfdaeed21a78d638ae9be922','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'},release_build_rerun=False,scope='source boundary inventory and inherited release pins; not fresh ELF verification')
x['build_source_pins']=[pin(R/f) for f in ['Cargo.lock','programs/r1-cost-probe/Cargo.toml','programs/r1-cost-probe/src/r1_pool_adapter.rs']]
x['lean_toolchain']='leanprover/lean4:v4.32.0; exact host binary SHA256 in every proof receipt'
x['features']='Inherited D182 production default/devnet and Pool pins; no new Rust feature selection or build in S2-X'
(E/'boundary-inventory.json').write_text(json.dumps(x,indent=2)+'\n')
print('Inventoried 54 Ops fields; SDK snapshot/write wrappers are outside AdapterRwModel')
