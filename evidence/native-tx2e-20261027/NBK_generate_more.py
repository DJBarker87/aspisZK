from pathlib import Path
import subprocess,difflib,json,hashlib
E=Path(__file__).resolve().parent;R='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';root='crates/aspis-statement/src/pool_v1/'
source=subprocess.check_output(['git','show',R+':'+root+'pair_forest_terminal.rs'],text=True)
a=source.index('    if common.master_account',source.index('pub fn validate_pool_v1_pair_forest_terminal_statement_v1'));b=source.index('    match statement',a)
prefix=source[a:b]
prefix=prefix.replace('common.master_account','master').replace('common.checkpoint_account','checkpoint').replace('common.selected_lane_account','selected').replace('common.output_lane','lane').replace('POOL_V1_PAIR_FOREST_LANE_COUNT','8').replace('return Err(','return Some(')
code='''use crate::pool_v1::pair_forest_terminal::PoolV1PairForestTerminalFormatErrorV1;
fn NBK_statement_prefix(master:[u8;32],checkpoint:[u8;32],selected:[u8;32],lane:u8)->Option<PoolV1PairForestTerminalFormatErrorV1>{
'''+prefix+'''None}
#[kani::proof]
fn NBK_statement_prefix_gate(){
 let m= kani::any();let c=kani::any();let s=kani::any();let l:u8=kani::any();
 let expected=if m==[0;32]||c==[0;32]||s==[0;32]{Some(PoolV1PairForestTerminalFormatErrorV1::NonZeroBinding)}else if l>=8{Some(PoolV1PairForestTerminalFormatErrorV1::InvalidOutputLane)}else{None};
 assert_eq!(NBK_statement_prefix(m,c,s,l),expected);
}
#[kani::proof]
fn NBK_asf8_domains_gate(){
 let mut output:[u8;1880]=kani::any();
 let base=output.as_mut_ptr();
 let late=&mut output[144..1664];
 assert_eq!(late.len(),1520);assert_eq!(late.as_mut_ptr(),base.wrapping_add(144));
 let payment=&mut output[1664..];
 assert_eq!(payment.len(),216);assert_eq!(payment.as_mut_ptr(),base.wrapping_add(1664));
 // Live deployment domain is inside late[32..832], offset 80, hence public[256..288].
 let domain=&mut output[144+32+80..144+32+112];
 assert_eq!(domain.len(),32);assert_eq!(domain.as_mut_ptr(),base.wrapping_add(256));
}
'''
jobs=[('NBK_K041','NBK_statement_prefix_gate'),('NBK_K042','NBK_asf8_domains_gate')]
for family,n,base in [('master',384,320),('checkpoint',192,112)]:
 for lane in range(8):
  start=base+8*lane;name=f'NBK_{family}_sequence{lane}'
  # Specialize exactly ONE iter_mut iteration; all rows and source bytes arbitrary.
  code+=f'''fn {name}(bytes:&[u8;{n}],rows:&mut[u64;8])->bool{{
   let sequence=&mut rows[{lane}];
   let start={base}+8*{lane};
   *sequence=u64::from_le_bytes(bytes[start..start+8].try_into().unwrap());
   {'*sequence>1048576' if family=='checkpoint' else 'false'}
}}
#[kani::proof]
fn {name}_gate(){{
 let bytes:[u8;{n}]=kani::any();let mut rows:[u64;8]=kani::any();let old=rows;
 let failed={name}(&bytes,&mut rows);let j:usize=kani::any();kani::assume(j<8);
 let word='''+' | '.join(f'((bytes[{start+i}] as u64)<<{8*i})' for i in range(8))+f''';
 assert_eq!(rows[j],if j=={lane}{{word}}else{{old[j]}});
 assert_eq!(failed,{'word>1048576' if family=='checkpoint' else 'false'});
}}
'''
  jobs.append((f'NBK_K{len(jobs)+41:03}',name+'_gate'))
code+='''#[kani::proof]
fn NBK_master_sequence_step_gate(){
 let rows:[u64;8]=kani::any();let lane:usize=kani::any();kani::assume(lane<8);
 let prior_bad:bool=kani::any();
 let sequence=&rows[lane];
 let bad=prior_bad || *sequence>crate::pool_v1::POOL_V1_PAIR_CAPACITY;
 assert_eq!(bad,prior_bad || rows[lane]>1048576);
}
#[kani::proof]
fn NBK_reserved_step_gate(){
 let raw:[u8;384]=kani::any();let mode:u8=kani::any();kani::assume(mode<3);
 let (start,end)=match mode{0=>(50usize,64usize),1=>(312,320),_=>(176,192)};
 let i:usize=kani::any();kani::assume(i<=end-start);let bad:bool=kani::any();
 let mut iter=raw[start+i..end].iter();
 let got=match iter.next(){None=>(i,bad,true),Some(byte)=>(i+1,bad||*byte!=0,false)};
 let expected=if i==end-start{(i,bad,true)}else{(i+1,bad||raw[start+i]!=0,false)};
 assert_eq!(got,expected);
}
'''
jobs += [('NBK_K059','NBK_master_sequence_step_gate'),('NBK_K060','NBK_reserved_step_gate')]
assert len(jobs)==20 and len(set(a for a,h in jobs))==20
(E/'NBK_more.rs.txt').write_text(code)
# Include the new module only in our frozen-source scratch parent; retain complete patch.
p=root+'pair_terminal.rs';old=subprocess.check_output(['git','show',R+':'+p],text=True)
new=old+'\n#[cfg(kani)]\n#[path="NBK_codecs.rs"]\nmod NBK_codecs;\n\n#[cfg(kani)]\n#[path="NBK_more.rs"]\nmod NBK_more;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+p,tofile='b/'+p))
for name in ['NBK_codecs','NBK_more']:
 s=(E/(name+'.rs.txt')).read_text();p=root+name+'.rs'
 patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/'+p))
(E/'NBK_harness_next.patch').write_text(patch)
(E/'NBK_MORE_JOBS.json').write_text(json.dumps(jobs,indent=2)+'\n')
(E/'NBK_MORE_PROVENANCE.json').write_text(json.dumps({'frozen_revision':R,'ASF8_prefix_source':prefix,'ASF8_original_range_sha256':hashlib.sha256(source[a:b].encode()).hexdigest(),'transformations':['project common fields after NBD source_common','return Err to Some; successful cut None','one sequence iteration specialized by lane; exposed capacity predicate','reserved any closure one iterator next step; explicit prefix bad invariant'],'scope':'source windows only; full enclosing callbacks and child bridges remain open'},indent=2)+'\n')
