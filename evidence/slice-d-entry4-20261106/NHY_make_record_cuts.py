from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];src=(R/'crates/aspis-statement/src/pool_v1/verifier_registry.rs').read_text();p=E/'NHY_registry.rs.txt';s=p.read_text().split('// NHY record cuts')[0]+'\n// NHY record cuts\n';rows=[]
errors=re.search(r'pub enum PoolV1VerifierRegistryFormatError \{(.*?)\n\}',src,re.S)[1];errors=re.findall(r'^    (\w+),',errors,re.M)
s+='fn NHY_any_error()->PoolV1VerifierRegistryFormatError{let tag:u8=kani::any();kani::assume(tag<'+str(len(errors))+');match tag{'+','.join(str(i)+'=>PoolV1VerifierRegistryFormatError::'+e for i,e in enumerate(errors[:-1]))+',_=>PoolV1VerifierRegistryFormatError::'+errors[-1]+'}}\n'
for label,ty in [('registry','VerifierRegistryV2'),('entry','VerifierRegistryEntryV2')]:
 fn='decode_verifier_registry_'+('entry_' if label=='entry' else '')+'v2';start=src.index('pub fn '+fn);a=src.index('let '+label+' = '+ty,start);b=src.index('    };',a)+6;literal=src[a:b];fields=re.findall(r'^        (\w+):',literal,re.M)
 cut='    let '+label+' = '+ty+' {\n'+''.join('        '+f+':input.'+f+',\n' for f in fields)+'    };\n'
 struct=re.search(r'pub struct '+ty+r' \{(.*?)\n\}',src,re.S)[1];types=dict(re.findall(r'pub (\w+): ([^,]+),',struct))
 arrays=[f for f in fields if types[f]=='[u8; 32]'];scalars=[f for f in fields if f not in arrays]
 anyvals=[]
 for f in fields:
  v='NHY_any_status()' if types[f]=='VerifierEntryStatusV1' else 'kani::any()';anyvals.append(f+':'+v)
 if label=='registry':
  s+='fn NHY_any_status()->VerifierEntryStatusV1{let tag:u8=kani::any();kani::assume(tag<4);match tag{0=>VerifierEntryStatusV1::Pending,1=>VerifierEntryStatusV1::Active,2=>VerifierEntryStatusV1::Paused,_=>VerifierEntryStatusV1::Retired}}\n'
 s+='fn NHY_any_'+label+'()->'+ty+'{'+ty+'{'+','.join(anyvals)+'}}\n'
 s+='fn NHY_'+label+'_byte(r:&'+ty+',field:u8,j:usize)->u8{match field{'+','.join(str(i)+'=>r.'+f+'[j]' for i,f in enumerate(arrays[:-1]))+',_=>r.'+arrays[-1]+'[j]}}\n'
 # Arbitrary complete input record is the joined pre-state of all independent
 # read32/word/status packets. Child reply includes every error constructor.
 for bad in [False,True]:
  n=label+'_record'+('_wrong' if bad else '')
  s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet(input:&{ty},reply:Result<(),PoolV1VerifierRegistryFormatError>,field:u8,j:usize)->bool{{
 kani::assume((field as usize)<{len(arrays)});kani::assume(j<32);
'''+cut+f''' let mut calls=0u8;
 let result=(||->Result<{ty},PoolV1VerifierRegistryFormatError>{{
  // Exact local logging oracle: immutable input record, full Result reply.
  calls+=1;
  let validation=reply;
  validation?;
  Ok({label})
 }})();
 let value=match (reply,&result){{
  (Err(e),Err(observed))=>e==*observed,
  (Ok(()),Ok(observed))=>NHY_{label}_byte(observed,field,j)==NHY_{label}_byte(input,field,j)
'''+''.join('    && observed.'+f+'==input.'+f+'\n' for f in scalars)+'''  ,_=>false};
 '''+f'calls=={2 if bad else 1} && value\n}}\n'+f'''#[kani::proof_for_contract({n}_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}_check(){{let input=NHY_any_{label}();let reply=if kani::any(){{Ok(())}}else{{Err(NHY_any_error())}};{n}_packet(&input,reply,kani::any(),kani::any());}}
'''
 rows.append(dict(function=fn,source_constructor_sha256=hashlib.sha256(literal.encode()).hexdigest(),fields=fields,arrays=arrays,scalars=scalars,errors=errors,cut='after all source field-read calls; source constructor same field order/types; all RHS substituted with input.FIELD on arbitrary full record pre-state',credit='SUPPORT_ONLY; root needs original read/state/callee association and native validator full-result law'))
p.write_text(s);x=json.loads((E/'NHY_NATIVE_INPUTS.json').read_text());x['crates/aspis-statement/src/pool_v1/NHY_registry.rs']=s;(E/'NHY_NATIVE_INPUTS.json').write_text(json.dumps(x));p=E/'NHY_SOURCE_PINS.json';x=json.loads(p.read_text());x['crates/aspis-statement/src/pool_v1/NHY_registry.rs']=hashlib.sha256(s.encode()).hexdigest();p.write_text(json.dumps(x,indent=1)+'\n');(E/'NHY_RECORD_CUTS.json').write_text(json.dumps(rows,indent=1)+'\n')
