from pathlib import Path
import ast,hashlib,json,os,re,subprocess,threading
H=Path('/home/dombarker/project-offloads/codex-pv-n7-20261027');E=H/'evidence'
def pin(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
B=H/'devnet_spend-patched'
raw=subprocess.check_output(['objdump','-d','-Mintel','--demangle',str(B)],text=True)
(H/'full-disassembly.txt').write_text(raw)
blocks=re.split(r'(?=^[0-9a-f]+ <)',raw,flags=re.M)
selected=[b for b in blocks if re.match(r'^[0-9a-f]+ <[^\n]*decode_raw_key_record',b)]
assert len(selected)==1
body=selected[0];(E/'decoder-disassembly.txt').write_text(body)
ins=[]
for line in body.splitlines():
 m=re.match(r'\s*([0-9a-f]+):\s+((?:[0-9a-f]{2} )+)\s*(.*)',line)
 if m:ins.append(dict(pc=m[1],instruction=m[3]))
assert not any(re.match(r'(j\w+|call\w*|div|idiv)\b',i['instruction']) for i in ins),ins
(E/'decoder.json').write_text(json.dumps(dict(binary=pin(B),full_disassembly=pin(H/'full-disassembly.txt'),instructions=ins,classification='clean fixed 64-byte raw record copy: no content predicate, table, Jcc, indirect control transfer, DIV/IDIV; memory offsets fixed relative to input/output pointers. CPU latency V371 retained.',encoding='raw bytes, not hex; no hex decoder required'),indent=2)+'\n')
# Pin every original build input and prove only the proposed host files differ.
inputs=json.loads((H/'build-inputs.json').read_text())['files'];changed=[]
for path,expected in inputs.items():
 assert pin(H/'base'/path)['sha256']==expected,path
 if pin(H/'patched'/path)['sha256']!=expected:changed.append(path)
assert sorted(changed)==['scripts/r1_devnet_spend.py','tools/r1-cost-probe/src/bin/devnet_spend.rs'],changed
(E/'source-comparison.json').write_text(json.dumps(dict(revision='0c9dc9a4ccd87cc9a4a6590842894a85e56581b2',checked=len(inputs),base_mismatches=[],patched_changes=changed,release_crates_programs_changes=[],scratch_fixture_helper='tools/r1-cost-probe/src/bin/pv_n7_requests.rs, audit-only added binary; not in proposed patch'),indent=2)+'\n')
# Ruling (l): actual retained artifact hashes, no inference from crate naming.
root=Path('/home/dombarker/project-offloads/codex-pv-op223-20261027')
items=[('default','build-default','aspis_r1_cost_probe_program.so','f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4'),('devnet','build-devnet-public-inputs-002','aspis_r1_cost_probe_program.so','63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299'),('Pool','build-pool','aspis_pool.so','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')]
rows=[]
for name,d,f,expected in items:
 row=dict(name=name,**pin(root/d/'artifacts'/f),expected=expected);row['matches']=row['sha256']==expected;assert row['matches'],row;rows.append(row)
(E/'elf-pins.json').write_text(json.dumps(dict(rows=rows,rebuilt=False,reason='Only standalone host binary and Python writer differ; all original crates/programs/build inputs byte-identical between scratch trees. Ruling (l) dependency/gate assessment in design. Retained pins freshly rehashed, not a new SBF reproducibility build.'),indent=2)+'\n')
# Execute the exact Python invoke function only, avoiding driver top-level RPC.
tree=ast.parse((H/'patched/scripts/r1_devnet_spend.py').read_text());node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='invoke')
ns=dict(SIGNER=str(B),json=json,os=os,subprocess=subprocess,threading=threading)
exec(compile(ast.Module(body=[node],type_ignores=[]),str(H/'patched/scripts/r1_devnet_spend.py'),'exec'),ns)
# RFC8032 test vector 1 is a public, unfunded signing fixture. Never use on-chain.
seed=bytes.fromhex('9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60')
pub=bytes.fromhex('d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a')
key=H/'RFC8032-public-fixture-key.json'
assert not key.exists();key.write_text(json.dumps(list(seed+pub)));key.chmod(0o600)
q=dict(keys=[str(key)],instructions=[],blockhash='11111111111111111111111111111111')
a=json.loads(subprocess.check_output([str(H/'devnet_spend-base')],input=json.dumps(q).encode(),timeout=30))
b=ns['invoke'](q);assert a==b
(E/'signing-fixture.json').write_text(json.dumps(dict(fixture='RFC8032 test vector 1, public unfunded; retained on host, no RPC',byte_identical=a==b,transaction_bytes=a['bytes'],transaction_sha256=hashlib.sha256(bytes.fromhex(a['hex'])).hexdigest(),signature=a['signature'],writer='exact patched Python invoke extracted with AST; original key file unchanged'),indent=2)+'\n')
# Public transport shape errors. Never mislabel these as private-content tests.
errors=[]
for label,data in [('short',bytes(63)),('extra',seed+pub+b'\0')]:
 rfd,wfd=os.pipe();os.write(wfd,data);os.close(wfd)
 r=subprocess.run([str(B)],input=json.dumps({**q,'key_bytes_fd':rfd}),text=True,capture_output=True,pass_fds=(rfd,),timeout=30);os.close(rfd)
 assert r.returncode!=0;errors.append(dict(case=label,exit=r.returncode,stderr=r.stderr))
(E/'shape-errors.json').write_text(json.dumps(errors,indent=2)+'\n')
print('decoder, source comparison, ELF pins, exact Python signing fixture, public shape errors: PASS')
