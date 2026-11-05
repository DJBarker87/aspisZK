"""Generate prefix-owned exact source cuts; never changes shipped files."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];S=(R/'crates/aspis-statement/src/pool_v1/verifier_registry.rs').read_text();p=E/'NHY_registry.rs.txt';base=p.read_text().split('// NHY generated decoder cuts')[0];source=[]
s=base+'\n// NHY generated decoder cuts\n'
for name,ty,L in [('registry_v1','VerifierRegistryV1',128),('entry_v1','VerifierRegistryEntryV1',192),('registry_v2','VerifierRegistryV2',256),('entry_v2','VerifierRegistryEntryV2',320)]:
 fn='decode_verifier_registry_'+('entry_' if name.startswith('entry') else '')+name[-2:];b=S.index('pub fn '+fn+'(');a=S.index('{',b);end=S.index('    let ',a);part=S[a+1:end];mapping={x:i+1 for i,x in enumerate(re.findall(r'return Err\(PoolV1VerifierRegistryFormatError::(\w+)\);',part))};cut=part
 for k,v in mapping.items():cut=cut.replace('return Err(PoolV1VerifierRegistryFormatError::'+k+');','return '+str(v)+';')
 s+=f'fn {name}_header(bytes:&[u8])->u8{{'+cut+'0}\n'
 # Independent direct byte predicates describe every first error on exact length.
 magic_name=re.search(r'bytes\[\.\.4\] != (\w+)',part)[1]
 magic=list(re.search(r'pub const '+magic_name+r': \[u8; 4\] = \*b"([^"]+)"',S)[1].encode())
 version_name=re.search(r'bytes\[4\] != (\w+)',part)[1]
 version=int(re.search(r'pub const '+version_name+r': u8 = (\d+);',S)[1])
 predicates=[('WrongLength',f'bytes.len()!={L}'),('WrongMagic',' || '.join(f'bytes[{i}]!={v}' for i,v in enumerate(magic))),('WrongVersion',f'bytes[4]!={version}')]
 if name.endswith('v2'):predicates.append(('InvalidDeploymentMode',f'bytes[{7 if name.startswith("entry") else 6}]!=1'))
 start,reserved=(120,8) if name=='registry_v1' else (184,8) if name=='entry_v1' else (249,7) if name=='registry_v2' else (314,6)
 predicates.append(('NonZeroReserved',('bytes[7]!=0 || ' if name=='registry_v1' else '')+' || '.join(f'bytes[{i}]!=0' for i in range(start,start+reserved))))
 expr='0'
 for label,pred in reversed(predicates):expr=f'if {pred} {{{mapping[label]}}} else {{{expr}}}'
 s+=f'fn {name}_header_ref(bytes:&[u8])->u8{{{expr}}}\n'
 for bad in [False,True]:
  n=name+'_header'+('_wrong' if bad else '')
  s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet(bytes:&[u8;{L}])->bool{{{name}_header(bytes){'!=' if bad else '=='}{name}_header_ref(bytes)}}
#[kani::proof_for_contract({n}_packet)] #[kani::unwind(10)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}_check(){{{n}_packet(&kani::any());}}
'''
 source.append(dict(function=fn,source_prefix_sha256=hashlib.sha256(part.encode()).hexdigest(),cut=n,transformation='replace only explicit return Err(ErrorLabel) by distinct u8 labels; stop at record constructor; actual constants and condition expressions retained',mapping=mapping,domain=f'exact borrowed length{L}; no full decoder credit'))
p.write_text(s);x=json.loads((E/'NHY_NATIVE_INPUTS.json').read_text());x['crates/aspis-statement/src/pool_v1/NHY_registry.rs']=s;(E/'NHY_NATIVE_INPUTS.json').write_text(json.dumps(x));p=E/'NHY_SOURCE_PINS.json';x=json.loads(p.read_text());x['crates/aspis-statement/src/pool_v1/NHY_registry.rs']=hashlib.sha256(s.encode()).hexdigest();p.write_text(json.dumps(x,indent=1)+'\n');(E/'NHY_DECODER_CUTS.json').write_text(json.dumps(source,indent=1)+'\n')
