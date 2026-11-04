from pathlib import Path
import json,hashlib,difflib,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];C='programs/r1-cost-probe/src/';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
old=(E/'NFW_syscall.rs.txt').read_text();a=old.index('fn syscall_bytes(){');b=old.index('\n#[kani::proof]',a+1)
body='''fn syscall_bytes(){
 // Symbolic zeroed allocations, one arbitrary byte per backing. No dense
 // fixed 57,607-byte array is materialized. The KMX/borrow frame supplies the
 // disjoint-memory value law; generic source/value association remains explicit.
 let sizes:[usize;5]=kani::any();let positions:[usize;5]=kani::any();let values:[u8;5]=kani::any();let mut i=0;while i<5{kani::assume(sizes[i]<=u32::MAX as usize);if sizes[i]>0{kani::assume(positions[i]<sizes[i]);}i+=1;}
 let mut d0=alloc::vec![0u8;sizes[0]];let mut d1=alloc::vec![0u8;sizes[1]];let mut d2=alloc::vec![0u8;sizes[2]];let mut d3=alloc::vec![0u8;sizes[3]];let mut d4=alloc::vec![0u8;sizes[4]];
 if sizes[0]>0{d0[positions[0]]=values[0];}if sizes[1]>0{d1[positions[1]]=values[1];}if sizes[2]>0{d2[positions[2]]=values[2];}if sizes[3]>0{d3[positions[3]]=values[3];}if sizes[4]>0{d4[positions[4]]=values[4];}
 let backing:[&[u8];5]=[&d0,&d1,&d2,&d3,&d4];let origin:[usize;5]=kani::any();let starts:[usize;5]=kani::any();let lengths:[usize;5]=kani::any();let mut i=0;while i<5{kani::assume(origin[i]<5);kani::assume(starts[i]<=sizes[origin[i]]);kani::assume(lengths[i]<=sizes[origin[i]]-starts[i]);i+=1;}
 let parts:[&[u8];5]=[&backing[origin[0]][starts[0]..starts[0]+lengths[0]],&backing[origin[1]][starts[1]..starts[1]+lengths[1]],&backing[origin[2]][starts[2]..starts[2]+lengths[2]],&backing[origin[3]][starts[3]..starts[3]+lengths[3]],&backing[origin[4]][starts[4]..starts[4]+lengths[4]]];
 let count:usize=if cfg!(NFW_badarg)||cfg!(NFW_invert){1}else{kani::any()};kani::assume(count<=5);let input=&parts[..count];let mut log=Log{reply:kani::any(),calls:0,parts:None};let result=syscall_cut(input,&mut log);let word:usize=if cfg!(NFW_invert){0}else{kani::any()};kani::assume(word<32);assert_eq!(log.calls,1);assert!((result[word]==log.reply[word])!=cfg!(NFW_invert));
 let seen=log.parts.unwrap();let same=seen.len()==input.len()&&core::ptr::eq(seen,input);assert!(same);
 if same&&count>0{let p:usize=kani::any();kani::assume(p<count);let at:usize=kani::any();let expected=if at<lengths[p]{if starts[p]+at==positions[origin[p]]{values[origin[p]]}else{0}}else{0};let actual=if at<seen[p].len(){seen[p][at]}else{0};assert_eq!(actual,expected);}
}
'''
code=old[:a]+body+old[b:];(E/'NFW_syscall.rs.txt').write_text(code)
x=json.loads((E/'NFW_NATIVE_INPUTS.json').read_text());x[C+'NFW_syscall.rs']=code;(E/'NFW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');x=json.loads((E/'NFW_SOURCE_PINS.json').read_text());x[C+'NFW_syscall.rs']=hashlib.sha256(code.encode()).hexdigest();(E/'NFW_SOURCE_PINS.json').write_text(json.dumps(x,indent=1)+'\n')
base=subprocess.check_output(['git','show',F+':'+C+'lib.rs'],cwd=R,text=True);lib=json.loads((E/'NFW_NATIVE_INPUTS.json').read_text())[C+'lib.rs'];patch=''.join(difflib.unified_diff(base.splitlines(True),lib.splitlines(True),fromfile='a/'+C+'lib.rs',tofile='b/'+C+'lib.rs'))+''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+C+'NFW_syscall.rs'));(E/'NFW_syscall.patch').write_text(patch)
(E/'NFW_K074_REVIEW.json').write_text(json.dumps(dict(attempt='NFW_K074',disposition='TIMEOUT; no credit for the 3717 dense-envelope shape',replacement='Same syscall_bytes name; symbolic zeroed Vec allocations up to u32::MAX, one arbitrary byte/window per backing, arbitrary overlapping subviews, and no large fixed-array initialization. KMX_CopyMeaning is imported unchanged, and NFW_BorrowFrame proves same-view, disjoint log/copy frames and sparse-cell laws first. Pointer/ownership validity and whole-value source/ABI interpretation remain explicit; no new global digest row is admitted from a sparse harness alone.'),indent=1)+'\n')
