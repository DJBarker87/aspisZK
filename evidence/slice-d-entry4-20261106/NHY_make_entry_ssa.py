from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];src=(R/'crates/aspis-statement/src/pool_v1/verifier_registry.rs').read_text();p=E/'NHY_registry.rs.txt';s=p.read_text().split('// NHY entry SSA return')[0]+'\n// NHY entry SSA return\n';ty='VerifierRegistryEntryV2';f=src[src.index('let entry = '+ty,src.index('pub fn decode_verifier_registry_entry_v2')):];literal=f[:f.index('    };')+6];fields=re.findall(r'^        (\w+):',literal,re.M);struct=re.search(r'pub struct '+ty+r' \{(.*?)\n\}',src,re.S)[1];types=dict(re.findall(r'pub (\w+): ([^,]+),',struct));arrays=[f for f in fields if types[f]=='[u8; 32]'];scalars=[f for f in fields if f not in arrays]
for bad in [False,True]:
 n='entry_ssa'+('_wrong' if bad else '')
 params='arrays:&[&[u8;32];'+str(len(arrays))+'],'+','.join(f+':'+types[f] for f in scalars)+',reply:Result<(),PoolV1VerifierRegistryFormatError>,field:u8,j:usize'
 s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet({params})->bool{{
 kani::assume((field as usize)<{len(arrays)});kani::assume(j<32);
 let entry={ty}{{'''+','.join(f+':'+('*arrays['+str(arrays.index(f))+']' if f in arrays else f) for f in fields)+'''};
 let result=(||->Result<'''+ty+''',PoolV1VerifierRegistryFormatError>{reply?;Ok(entry)})();
 let good=match (reply,&result){(Err(expected),Err(actual))=>expected==*actual,(Ok(()),Ok(value))=>NHY_entry_byte(value,field,j)==arrays[field as usize][j]
'''+''.join(' && value.'+f+'=='+f+'\n' for f in scalars)+''',_=>false};
 '''+('!' if bad else '')+'good\n}\n'+f'''#[kani::proof_for_contract({n}_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}(){{let arrays=['''+','.join('&kani::any::<[u8;32]>()' for _ in arrays)+'''];let reply=if kani::any(){Ok(())}else{Err(NHY_any_error())};'''+n+'_packet(&arrays,'+','.join('NHY_any_status()' if types[f]=='VerifierEntryStatusV1' else 'kani::any()' for f in scalars)+',reply,kani::any(),kani::any());}\n'
p.write_text(s);(E/'NHY_ENTRY_SSA.json').write_text(json.dumps(dict(replacement_for='K092 timed-out record-input/result packet',change='Real after-read pre-state expressed as independent SSA field arrays/scalars, no extra whole input record or returned-record generator copy; original constructor and full Result preserved. Whole frozen source root/model first-error association still OPEN.',array_fields=arrays,scalar_fields=scalars,source_constructor_sha256=hashlib.sha256(literal.encode()).hexdigest(),harnesses=['entry_ssa','entry_ssa_wrong'],credit='SUPPORT_ONLY until every whole decoder/native/model association is complete'),indent=1)+'\n');print('prepared entry SSA packet, runner publication deferred')
