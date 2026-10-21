#!/usr/bin/env python3
"""Exact frozen stage1 source cut; real SDK/account and statement carriers."""
from pathlib import Path
import hashlib,json,subprocess,sys
R=Path(__file__).resolve().parents[2]
O=Path(sys.argv[1]); (O/'src').mkdir(parents=True,exist_ok=True)
REV='b2727acd3abf79315d18b754a260f58f4b1c6326'
P='programs/r1-cost-probe/src/r1_pool_adapter.rs'
s=subprocess.check_output(['git','-C',str(R),'show',REV+':'+P],text=True)
def cut(name):
 a=s.index('fn '+name); b=s.index('{',a); e=b+1; d=1
 while d:
  d+=(s[e]=='{')-(s[e]=='}');e+=1
 return s[a:e]
names=['readonly_buffer_meta_ok','require_readonly_buffer','require_verifier_checkpoint','require_distinct_accounts','stage1']
chunks={n:cut(n) for n in names}
# No source substitutions: same names resolved to typed, explicit child boundaries.
code=(R/'tools/s126-sdk-20261021/prelude.rs').read_text()+'\nmod adapter {\nuse super::*;\n'+'\n\n'.join(chunks.values())+'\npub fn run(p:&Pubkey,a:&[AccountInfo],d:&[u8])->ProgramResult {stage1(p,a,d)}\n}\n'+(R/'tools/s126-sdk-20261021/harness.rs').read_text()
(O/'src/lib.rs').write_text(code)
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-real-sdk-boundary"
version="0.0.0"
edition="2021"
[workspace]
[features]
cu-profiling=[]
[dependencies]
solana-program="=2.3.0"
aspis-statement={path="REPO/crates/aspis-statement",features=["r0","pool-v1-kernel"]}
[profile.release]
opt-level=3
overflow-checks=true
'''.replace('REPO',str(R)))
pins=dict(schema='focused-extractor-proof-packet-v1',freeze=REV,path=P,source_sha256=hashlib.sha256(s.encode()).hexdigest(),declarations={n:dict(source=x,sha256=hashlib.sha256(x.encode()).hexdigest()) for n,x in chunks.items()},code_sha256=hashlib.sha256(code.encode()).hexdigest(),boundaries=['decoder','statement validator','afterstate encoder','tx1/checkpoint size'],qualification='Real solana-program AccountInfo/Rc/RefCell/Ref/RefMut, real ProgramError and actual statement/Public carriers. Child semantics remain explicit. This is not an Aeneas SDK translation or global soundness proof.')
(O/'source-cut.json').write_text(json.dumps(pins,indent=2)+'\n')
print(json.dumps({'sha256':pins['code_sha256'],'declarations':names}))
