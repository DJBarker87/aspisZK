import hashlib,json,sys
from pathlib import Path
H=Path(sys.argv[1]); P=H.parent/'codex-cx-pin-20261020'
expected={'verifier/aspis_r1_cost_probe_program.so':'dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34','verifier/linked.elf':'cff391a766c1085e4c1673268c0e6ace53a9e1b3ae9ef406bab5fb978d755486','pool/aspis_pool.so':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548','pool/linked.elf':'9121c1fc52a3b7f17146e57102979985ce37af1866407234dcfd3e37cd45a4cf'}
rows=[]
for n,sha in expected.items():
 p=H/'artifacts'/n; b=p.read_bytes(); actual=hashlib.sha256(b).hexdigest(); assert actual==sha,(n,actual)
 rows.append(dict(path=str(p),sha256=actual,bytes=len(b)))
p=P/'extraction-freeze/Stage2.llbc'; b=p.read_bytes(); assert hashlib.sha256(b).hexdigest()=='f11e40b4119578eee1ebef90874f436dc35b1076f6db27baaa92a79c0919538d'
rows.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),format='LLBC JSON, not ELF'))
reg=H.parent/'active-mask-basis-sbf-20261017/artifacts/aux-current/registry/aspis_registry.so'; rb=reg.read_bytes(); rh=hashlib.sha256(rb).hexdigest(); assert rh=='7ad46f0d4b102a7c9699149d23bf6e065b6151feeaca95977d0a3146167d01ab'; rows.append(dict(path=str(reg),sha256=rh,bytes=len(rb)))
(H/'pins.json').write_text(json.dumps(rows,indent=1)+'\n');print(json.dumps(rows,indent=1))
