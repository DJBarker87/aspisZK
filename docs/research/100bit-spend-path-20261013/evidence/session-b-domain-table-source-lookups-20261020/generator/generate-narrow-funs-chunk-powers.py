import hashlib,json,re,sys
from pathlib import Path
P=2147483647; GEN=(2,1268011823)
source=Path('/Users/dominic/ZK/docs/research/100bit-spend-path-20261013/evidence/session-b-fibre-point-extraction-20261019/sources/Funs-chunked-adapter.lean')
src=source.read_text(); assert hashlib.sha256(source.read_bytes()).hexdigest()=='f1c1765883a09cc9d9ec926127efbd3810f9f60cf5c77893d35b633e5288bb3f'
def rev(w,x): return int(f'{x:0{w}b}'[::-1],2)
def mul(x,y): return ((x[0]*y[0]-x[1]*y[1])%P,(x[0]*y[1]+x[1]*y[0])%P)
def powc(n): return powc_cache[n] if n in powc_cache else None
powc_cache={0:(1,0)}
def cpow(n):
 if n in powc_cache:return powc_cache[n]
 y=cpow(n//2); z=mul(y,y) if n%2==0 else mul(mul(y,y),GEN);powc_cache[n]=z;return z
base=json.loads(Path('/tmp/r17-funs-narrow-a01-power-v2-20261020/config.json').read_text())
baseRoots=base['lean_path']
cert_hashes={'A00':'96ed6932581517707e17434fc6defb7f2da6958db8a07b5a20c565abeff6b259','B00':'476b0d7fe2ace3050ac5c1211da040a60060566cbebc798e6f1081b7070c4635',
'A01':'10d2c93ea00247c9f599bad8a5d7281657dd4766c01feaa7bd51b2e4cf5855d4','A02':'796220893ae824d157db7f000d7ff866432998d29eac9ac7b2bf4ab62f53322a','A03':'9606947997bc52c29d3d0ba74b1ba8443883743701f74d42621ecae7a301ac4b','A04':'06160df515e4a0bbf5674616bffe2f840eb2e091c8761354f4ec293c401f5aa7','A05':'26d3bfa1a7bfede51e92a3a21daecf4cbe277099b069e486328e93a485df2764','A06':'d2aa90576d7b8818a034b708b747dc8e874f44db52b50d3ac320cc7066112906','A07':'fcbfd4f2ced5074c42b1ae922a3c3e156f34a0939c500dd7b40367e33ede25cd','A08':'668200e572ce2e09c322e36b7f116a674274ec055feb69ea616d5903ff83e2d9','A09':'dd522b334253a21b20db593dcacedbfaa06da37f1c59b5d1e388c31a8042c93f','A10':'afbb61e9877e766ad35a1688ff9688ae44a9974fc94180f10734c084fb898ae3','A11':'1f8eb53bb81248f7720ac2cda022f1c24780f3b004d6d4e6d2e63603ec1a4d1f','A12':'64cd9a6dca78c588fbd71be9f91be0e7397d4f70f92a6a0826901016f9eddc74','A13':'5506f098528fad2bad6cb0a2c0f1ef3953d0132455a3fec86be2bc992274efd9','A14':'5f9d91383dfa81fa0a7acbb4190d1aaf8cfabe5103057acc5c27690c4b2ba55b','A15':'88428fb329fe57c95932058cdf154d20f6f2536ecc45d765193e9f6a91788c5c',
'B01':'38090bd4635cf6edbbb6ba9d064197a07e39bb3c77b8f6a48a4fd917713fba53','B02':'ed06e7af99189196e68c0343eca7e2fa0a7e81b792326490a1fb5b4b0f20dbd8','B03':'afeb3cd5f7a2d0fdc06e8fd5c0b13ecce69cb16856b31e042b040a0a5d19e91c','B04':'ded72175abd6875bb7ae85472defebac26c229d7b1854eae5dc9fe91a67268a9','B05':'43bbe56480d524251ea773b473eafe58884bd348e24e0b4a3255b679f4189c87','B06':'a1bc39513f4fcf8db683b50cfcbd7187fd4e9b06b2b3123b1fb43d50ebc802f3','B07':'06d93682a553833dfd2284e1837b7fb4918ed827b6da56165ec49cdc5db99546','B08':'b514d79f86a7b5b79ec779bad09676c87e4439c849ee9493fe702c12d541611c','B09':'014386185eb4d8d55e7a4826da000c3302c5d9028f68c215c0b02f2014bf5b57','B10':'773902a75428a539d4bc04dcea5340a45bf65ebd7a6a9e1654385484cf34d8fa','B11':'c6dccc07190b809b1bb1e406d4fb9ae455248b3fd9a48b2e1364ec8ff2d776ab','B12':'e91b5ec760c073c6bb635226de87e8a3dea0f9369fcc511736ddf2ce34404e02','B13':'6c6e5364ddf4dc3214e7eff5652e008166ba845a102caf2968635446621f947d','B14':'8559c79df865b69a1e5debd67eb315e19499885d6c07f90370956104f454e864','B15':'e074f6c3f61ea84c92ad4cd046fb5d13f8c4f08bbd4e9765964bdf300de96822'}
root=Path('/tmp/r17-funs-narrow-allchunks-v3-20261020'); (root/'sources').mkdir(parents=True,exist_ok=True)
mods=[]
for table in 'AB':
 for chunk in range(16):
  if table=='A' and chunk==1: continue
  key=f'{table}{chunk:02d}'
  prefix=f'def fast_domain.TABLE_{table}_chunk_{chunk:02d} :'
  line=next(x for x in src.splitlines() if x.startswith(prefix))
  pairs=[tuple(map(int,x)) for x in re.findall(r'\((\d+)#u32, (\d+)#u32\)',line)]
  assert len(pairs)==32
  exps=[(2**10+2**21*rev(9,chunk*32+i)) if table=='A' else 2**12*rev(9,chunk*32+i) for i in range(32)]
  assert [cpow(e) for e in exps]==pairs, key
  cert=f'R17Table{table}Chunk{chunk:02d}Certificate'; power='leftExponent' if table=='A' else 'rightExponent'
  ns=f'R17NarrowFuns{table}{chunk:02d}ChunkPower'; mod=ns
  lines=[f'import AspisR1QueryGeometryActual.Funs',f'import {cert}','', 'set_option autoImplicit false','',f'namespace {ns}','']
  for i,(x,y) in enumerate(pairs):
   e=exps[i]; idx=chunk*32+i; arr=f'AspisR1QueryGeometryActual.fast_domain.TABLE_{table}_chunk_{chunk:02d}'
   lines += [f'theorem cell_{i:02d}_circle_power :',f'    R17TableBasePowerBridge.decode ({cert}.toNatC (⟨({arr}[{i}]!).1.val, ({arr}[{i}]!).2.val⟩ : R17TableBasePowerProbe.C)) =',f'      R17TableBasePowerBridge.zPow (R17TableBasePowerBridge.decode ({cert}.toNatC R17TableBasePowerProbe.gen))',f'        (R17TableExponentDomainBridge.{power} {idx}) := by',f'  have hcell : (({arr}[{i}]!).1.val, ({arr}[{i}]!).2.val) = ({x}, {y}) := rfl',f'  have hC : (⟨({arr}[{i}]!).1.val, ({arr}[{i}]!).2.val⟩ : R17TableBasePowerProbe.C) = ⟨{x}, {y}⟩ := by','    have h₁ := congrArg Prod.fst hcell','    have h₂ := congrArg Prod.snd hcell','    cases h₁','    cases h₂','    rfl',f'  rw [hC]',f'  rw [← {cert}.entry_{i:02d}]',f'  exact {cert}.fastPow_decode_zPow _','',f'#print axioms cell_{i:02d}_circle_power','']
  lines += [f'end {ns}','']
  out='\n'.join(lines); path=root/'sources'/f'{mod}.lean'; path.write_text(out)
  imp={"AspisR1QueryGeometryActual.Funs":"fefca8beeefd8d413083c8499ee7d6b026e2275207a833364a2c2301561fcc17",cert:cert_hashes[key]}
  # Existing path ordering, adding every cert-root ahead of rest; each cert is unique module.
  cert_roots=[]
  if table=='A' and chunk==0: cert_roots.append('/home/dombarker/project-offloads/r17-table-a-chunk00-v7-20261019/attempt/objects')
  elif table=='B' and chunk==0: cert_roots.append('/home/dombarker/project-offloads/r17-table-b-chunk00-v1-20261020/attempt/objects')
  else: cert_roots.append(f'/home/dombarker/project-offloads/r17-table-chunks-v1-20261020/{table}{chunk:02d}/attempt/objects')
  leanpath=[baseRoots[0],*cert_roots,*baseRoots[1:]]
  cfg={**base,"unit":f"r17-funs-{key.lower()}-power-v3-20261020","source_revision":f"Actual narrow-Funs lookup power projection for TABLE_{table}_chunk_{chunk:02d}; accepted certificate reused, Funs body adapter ca34b291...", "lean_path":leanpath,"stages":[{"phase":"power","module":mod,"source":f"sources/{mod}.lean","source_sha256":hashlib.sha256(out.encode()).hexdigest(),"direct_imports":imp}]}
  # target archive setup
  kit=root/key; kit.mkdir(exist_ok=True); (kit/'sources').mkdir(exist_ok=True); (kit/'sources'/f'{mod}.lean').write_text(out); (kit/'config.json').write_text(json.dumps(cfg,indent=2,sort_keys=True)+'\n')
  for filename in ('run-admitted.py','run-stage.py'):
   (kit/filename).write_bytes(Path('/tmp/r17-funs-narrow-a01-power-v2-20261020',filename).read_bytes())
  mods.append({'table':table,'chunk':chunk,'module':mod,'source':str(path),'sha256':hashlib.sha256(out.encode()).hexdigest(),'certificate':cert,'certificate_sha256':cert_hashes[key]})
(root/'generated-manifest.json').write_text(json.dumps(mods,indent=2)+'\n')
print('generated',len(mods),'chunks')
