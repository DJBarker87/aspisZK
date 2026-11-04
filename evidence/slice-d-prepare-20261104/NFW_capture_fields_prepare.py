from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=E/'NFW_prepared_native_prepare.py';s=p.read_text()
assert 'fn capture_prepared(' not in s
s=s.replace("newbody=body.replace", "newbody=body.replace",1)
pos=s.index("code='''use super::*;")
s=s[:pos]+'''newbody=newbody.replace('Ok(Box::new(Prepared{','let value=Prepared{').replace('claim,state:t.state}))','claim,state:t.state};let value=capture_prepared(value,sem,t.ops);Ok(Box::new(value))')
'''+s[pos:]
s=s.replace('struct Ops {empty_audit:bool,','struct Ops {output_facet:usize,output_word:usize,output_index:usize,empty_audit:bool,').replace('Ops{empty_audit:false,','Ops{output_facet:5,output_word:0,output_index:0,empty_audit:false,')
s=s.replace('let mut o=ops(slot);','let mut o=ops(slot);o.output_facet=if cfg!(NFW_CAPTURE_ALL){let f:usize=kani::any();kani::assume(f>=5&&f<=15);f}else{facet};o.output_word=word;o.output_index=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(o.output_index<match o.output_facet{7|12=>2,8=>22,10=>64,11=>10,13=>32,_=>1});')
s=s.replace('if facet==16||facet==17{return;}','if facet==16||facet==17||cfg!(NFW_CAPTURE_FIELDS){return;}')
code='''
fn capture_prepared(p:Prepared,sem:&crate::r1_semantic::Verified<Hash>,o:&mut Ops)->Prepared{
 if cfg!(NFW_CAPTURE_FIELDS){let word=o.output_word;let i=o.output_index;
 let value=match o.output_facet{
 5=>p.gamma.to_limbs()[word]==o.scalars[0].to_limbs()[word],
 6=>p.kappa.to_limbs()[word]==o.scalars[1].to_limbs()[word],
 7=>p.alpha[i].to_limbs()[word]==o.scalars[i+2].to_limbs()[word],
 8=>p.queries[i]==o.queries[i],9=>p.claim.to_limbs()[word]==o.claim.to_limbs()[word],
 10=>p.roots[i/32][i%32]==sem.roots[i/32][i%32],11=>p.semantic_alpha[i]==sem.alpha[i],
 12=>p.z[i]==sem.z[i],13=>p.state[i]==o.states[6][i],14=>p.rho==o.rho,_=>p.variant==Variant::S2};
 assert!(value!=cfg!(NFW_invert));kani::assume(false);}
 p
}
'''
pos=s.index('# A new child module');s=s[:pos]+'code+='+repr(code)+'\n'+s[pos:];p.write_text(s)
p=E/'NFW_run.py';s=p.read_text();needle="if os.environ.get('NFW_EMPTY_RHO'):env['RUSTFLAGS']+=' --cfg NFW_EMPTY_RHO'";s=s.replace(needle,needle+"\n if os.environ.get('NFW_CAPTURE_FIELDS'):env['RUSTFLAGS']+=' --cfg NFW_CAPTURE_FIELDS'\n if os.environ.get('NFW_CAPTURE_ALL'):env['RUSTFLAGS']+=' --cfg NFW_CAPTURE_ALL'");p.write_text(s)
(E/'NFW_K063_REVIEW.json').write_text(json.dumps(dict(attempt='NFW_K063',disposition='TIMEOUT; no field-output credit',replacement='Same original prepared_facet5 name. Observe the exact source Prepared record at the Box::new argument boundary, end the observation path, and combine all 11 field classes under one arbitrary projection. NFW_PreparedFields.source is the same adopted record constructor. Box allocation/value transport remains an explicit reclassification within retained std/allocator/ABI and P6/D188 option-A semantic-transport trust, not a removed premise. Normal Result/scratch root is still K027/K028; this is an argument-window packet, not a whole native-output equality assumption.'),indent=1)+'\n')
