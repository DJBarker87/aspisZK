from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent.parent
p=E/'native-poseidon/lib.rs';s=p.read_text();records=[]
for module in ['native','retained']:
 start=s.index('mod '+module+' {');f=s.index('fn external_linear_lazy(state:',start);a=s.index('    let mut group',f);b=s.index('    let sums:',a);c=s.index('    let mut index',b);end=s.index('\nfn internal_linear_lazy',c)
 group=s[a:b];sums=s[b:c];finish=s[c:end].rsplit('\n}',1)[0]
 groupbody=group[group.index('        let start'):group.rindex('        group += 1;')]
 finishbody=finish[finish.index('        let limbs'):finish.rindex('        index += 1;')]
 additions='\n pub fn group_cut(state:&mut [QM31;16],group:usize) {\n'+groupbody+'\n }\n'
 additions+=' pub fn sums_cut(state:&[QM31;16])->[[u64;4];4] {\n'+sums+'sums\n }\n'
 additions+=' pub fn finish_cut(state:&mut [QM31;16],sums:[[u64;4];4],index:usize) {\n'+finishbody+'\n }\n'
 marker=' pub fn row(input:';pos=s.index(marker,start);s=s[:pos]+additions+s[pos:]
 records.append(dict(module=module,group_sha=hashlib.sha256(groupbody.encode()).hexdigest(),sums_sha=hashlib.sha256(sums.encode()).hexdigest(),finish_sha=hashlib.sha256(finishbody.encode()).hexdigest()))
pos=s.index('#[cfg(kani)] mod proofs');s=s[:pos]+s[pos:].replace(' use super::*;',''' use super::*;
 #[kani::proof] #[kani::unwind(100)] fn external_group_cut() {
  let raw:[[u32;4];16]=kani::any();let group:u8=kani::any();kani::assume(group<4);
  let mut n:[field::QM31;16]=unsafe{std::mem::transmute(raw)};let mut r=n;
  native::group_cut(&mut n,group as usize);retained::group_cut(&mut r,group as usize);
  let k:u8=kani::any();kani::assume(k<16);assert_eq!(n[k as usize],r[k as usize]);
 }
 #[kani::proof] #[kani::unwind(100)] fn external_sums_cut() {
  let raw:[[u32;4];16]=kani::any();let n:[field::QM31;16]=unsafe{std::mem::transmute(raw)};
  assert_eq!(native::sums_cut(&n),retained::sums_cut(&n));
 }
 #[kani::proof] #[kani::unwind(100)] fn external_finish_cut() {
  let raw:[[u32;4];16]=kani::any();let sums:[[u64;4];4]=kani::any();
  for c in 0..4 {for w in 0..4 {kani::assume(sums[c][w] < (1u64<<34));}}
  let index:u8=kani::any();kani::assume(index<16);
  let mut n:[field::QM31;16]=unsafe{std::mem::transmute(raw)};let mut r=n;
  native::finish_cut(&mut n,sums,index as usize);retained::finish_cut(&mut r,sums,index as usize);
  let k:u8=kani::any();kani::assume(k<16);assert_eq!(n[k as usize],r[k as usize]);
 }
''',1)
p.write_text(s);(E/'external-cut-bindings.json').write_text(json.dumps(records,indent=2)+'\n')
