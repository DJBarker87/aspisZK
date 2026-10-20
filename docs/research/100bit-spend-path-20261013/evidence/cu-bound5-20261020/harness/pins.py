"""Assert independently rebuilt candidate artifacts and default/devnet identity."""
import hashlib,json,sys
from pathlib import Path
import sbf_slack as S
H=Path(sys.argv[1]); expected={
'verifier/aspis_r1_cost_probe_program.so':'f9ecbc275b71cf55886351d9445f93e44198d400f7c519573b8f44c9cdb91ae3',
'verifier/linked.elf':'a769ea0bc90f04faa282632e09b09e06e27867582ec13323624e2585108a076f',
'verifier-devnet/aspis_r1_cost_probe_program.so':'3f21a42fa6376edf68be160894c4be50db1940e13234a99934127dd49a06f851',
'verifier-devnet/linked.elf':'53a56ad9e1671a433ca9bd80ee7d0ad2372cc3d3eb219b3a82d3f95b188a79a8',
'pool/aspis_pool.so':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548',
'pool/linked.elf':'9121c1fc52a3b7f17146e57102979985ce37af1866407234dcfd3e37cd45a4cf'}
rows=[]
for n,sha in expected.items():
 p=H/'artifacts'/n; b=p.read_bytes(); actual=hashlib.sha256(b).hexdigest(); assert actual==sha,(n,actual)
 rows.append(dict(path=str(p),sha256=actual,bytes=len(b)))
a=(H/'artifacts/verifier/aspis_r1_cost_probe_program.so').read_bytes();b=(H/'artifacts/verifier-devnet/aspis_r1_cost_probe_program.so').read_bytes()
def text(b):
 t=next(t for t in S.elf_sections(b) if t['name']=='.text');return b[t['offset']:t['offset']+t['size']]
assert text(a)==text(b)
x=bytearray(a)
for offset in [1492256,1492288]: x[offset:offset+32]=b[offset:offset+32]
assert bytes(x)==b
(H/'pins.json').write_text(json.dumps(dict(artifacts=rows,default_devnet_text_identical=True,id_slot_offsets=[1492256,1492288],id_patch_reconstructs_devnet=True),indent=1)+'\n')
print('All six candidate ELF pins reproduced; text and ID-slot reconstruction pass')
