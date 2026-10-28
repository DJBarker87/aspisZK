from pathlib import Path
p=Path('evidence/native-decref2-20261028/NCX_instrument.py');s=p.read_text()
needle=" d['crates/aspis-statement/src/NCX_native.rs']=n"
s=s.replace(needle,''' for key,name in [('registry','VerifierRegistryV2'),('entry','VerifierRegistryEntryV2')]:
  fs=fields[name];expr=[]
  for i,f in enumerate(fs):
   cmp='eq_VerifierEntryStatusV1(&a.status,&b.status)' if f=='status' else f'a.{f}[j]==b.{f}[j]' if f in ['pool','authority','policy_binding','registry_program','loader_program','programdata_address','executable_hash','verifier_program','profile_binding','release_binding','expected_upgrade_authority'] else f'a.{f}==b.{f}'
   expr.append(str(i)+'=>'+cmp)
  n+=f'pub fn eq_{key}_coord(a:&Result<{name},PoolV1VerifierRegistryFormatError>,b:&Result<R::{name},R::PoolV1VerifierRegistryFormatError>,field:usize,j:usize)->bool{{match (a,b){{(Ok(a),Ok(b))=>match field{{'+','.join(expr)+',_=>false},(Err(a),Err(b))=>eq_PoolV1VerifierRegistryFormatError(a,b),_=>false}}\\n'
''' +needle)
needle=" shape=os.environ.get('NCX_SHAPE','registry')"
s=s.replace(needle,''' for key,name,fun,size in [('registry','VerifierRegistryV2','decode_verifier_registry_v2',256),('entry','VerifierRegistryEntryV2','decode_verifier_registry_entry_v2',320)]:
  prop='!*r' if negative else '*r'
  n+=f'#[kani::requires(b.len()=={size} && field<{len(fields[name])} && j<32)]\\n#[kani::modifies()]\\n#[kani::ensures(|r:&bool|{prop})]\\nfn NCX_{key}_window(b:&[u8],field:usize,j:usize)->bool{{aspis_statement::NCX_native::eq_{key}_coord(&{fun}(b),&aspis_statement::NCX_reference::{fun}(b),field,j)}}\\n'
  n+=f'#[kani::proof_for_contract(NCX_{key}_window)]\\n'+attrs+f'#[kani::unwind(34)]\\nfn NCX_{key}_window_contract(){{let b:[u8;{size}]=kani::any();let f:usize=kani::any();let j:usize=kani::any();kani::assume(f<{len(fields[name])} && j<32);let _=NCX_{key}_window(&b,f,j);}}\\n'
''' +needle)
p.write_text(s)
