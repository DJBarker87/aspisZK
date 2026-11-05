from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;R=E.parents[1];source=(R/'crates/aspis-statement/src/pool_v1/verifier_registry.rs').read_text();p=E/'NHY_registry.rs.txt';s=p.read_text().split('// NHY record argument cuts')[0]+'\n// NHY record argument cuts\n';rows=[]
for label,ty in [('registry','VerifierRegistryV2'),('entry','VerifierRegistryEntryV2')]:
 fn='decode_verifier_registry_'+('entry_' if label=='entry' else '')+'v2';a=source.index('let '+label+' = '+ty,source.index('pub fn '+fn));b=source.index('    };',a)+6;literal=source[a:b];fields=re.findall(r'^        (\w+):',literal,re.M);struct=re.search(r'pub struct '+ty+r' \{(.*?)\n\}',source,re.S)[1];types=dict(re.findall(r'pub (\w+): ([^,]+),',struct));arrays=[f for f in fields if types[f]=='[u8; 32]'];scalars=[f for f in fields if f not in arrays]
 cut='let '+label+' = '+ty+'{'+','.join(f+':input.'+f for f in fields)+'};'
 for bad in [False,True]:
  n=label+'_args'+('_wrong' if bad else '')
  s+=f'''#[kani::ensures(|r|*r)] #[kani::modifies()]
fn {n}_packet(input:&{ty},field:u8,j:usize)->bool{{
 kani::assume((field as usize)<{len(arrays)});kani::assume(j<32);
 {cut}
 // A local immutable observation of the exact constructed validator argument.
 let log=NHY_{label}_byte(&{label},field,j){'^1' if bad else ''};
 log==NHY_{label}_byte(input,field,j)
'''+''.join(' && '+label+'.'+f+'==input.'+f+'\n' for f in scalars)+f'''}}
#[kani::proof_for_contract({n}_packet)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn {n}_check(){{{n}_packet(&NHY_any_{label}(),kani::any(),kani::any());}}
'''
 rows.append(dict(function=fn,source_constructor_sha256=hashlib.sha256(literal.encode()).hexdigest(),all_fields=fields,scalar_fields=scalars,array_fields=arrays,domain='Every typed input record, any selected field and j<32; observations independent of validator reply; no success restriction',negative='corrupt one observed argument byte, all scalar and frame assertions unchanged'))
p.write_text(s);(E/'NHY_RECORD_ARGUMENTS.json').write_text(json.dumps(rows,indent=1)+'\n')
# Intentionally publish to the runner only when no other native queue is staging.
if __name__=='__main__':print('prepared record argument cuts; runner publication deferred')
