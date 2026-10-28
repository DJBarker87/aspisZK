from pathlib import Path
import subprocess,difflib,tempfile,hashlib,json
E=Path(__file__).resolve().parent;oldE=E.parent/'native-tx2h-20261028';p='crates/aspis-r1-cost-probe/src/fast_dots.rs'
paths=[p,'crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/fast_pairing.rs']
with tempfile.TemporaryDirectory() as d:
 for f in paths:
  q=Path(d)/f;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(subprocess.check_output(['git','show','4bb3b3f5:'+f],text=True))
 for patch in ['NBQ_u06_initial.patch','NBQ_u06b.patch','NBQ_u06c.patch','NBQ_u06d.patch','NBQ_u06e.patch','NBQ_u07.patch','NBQ_cells.patch','NBQ_tail.patch']:
  subprocess.run(['git','apply','-'],input=(oldE/patch).read_text(),cwd=d,text=True,check=True)
 s=(Path(d)/p).read_text()
s+=''.join(l[1:] for l in (E/'NBS_joined.patch').read_text().splitlines(True) if l.startswith('+') and not l.startswith('+++'))
frozen=subprocess.check_output(['git','show','4bb3b3f5:'+p],text=True)
cut=frozen.split('        let mut tail=EbyKDot::new();',1)[1].split('value.add(tail.finish())',1)[0]
cut='        let mut tail=EbyKDot::new();'+cut+'value.add(tail.finish())'
(E/'NBS_TAIL_WINDOW.json').write_text(json.dumps(dict(source=p,revision='4bb3b3f5',exact_tail_sha256=hashlib.sha256(cut.encode()).hexdigest(),source_window=cut,observation='three chained pushes, finish and actual final addition; no 26-term prefix'),indent=2)+'\n')
t=r'''
#[cfg(kani)] mod NBS_tail {
 use super::*;
 static mut CALLS:usize=0;static mut DPTR:*mut EbyKDot=core::ptr::null_mut();
 static mut GPTR:*const WideExact=core::ptr::null();static mut QPTR:*const u8=core::ptr::null();static mut SLOT:usize=0;
 static mut OUTPUT:[u32;8]=[0;8];
 fn word(q:&[u8;608],at:usize)->u32 {u32::from_le_bytes([q[at],q[at+1],q[at+2],q[at+3]])}
 fn push(s:&mut EbyKDot,v:WideExact,k:QM31)->Result<(),()>{unsafe{
  let c=CALLS;assert!(c<3);assert!(crate::fast_pairing::NBQ_count(s)==c);
  if c==0{DPTR=s;}else{assert!(core::ptr::eq(s,DPTR));}
  let gi=if c==0{28}else{25+c};let expect=(*GPTR.add(gi)).to_limbs();let value=v.to_limbs();
  let j:usize=kani::any();kani::assume(j<8);assert!(value[j]==expect[j]);
  let q=&*(QPTR as *const [u8;608]);let at=if c==0{SLOT*120+104}else{480+SLOT*32+(c-1)*16};
  assert!(k.c0.a.0==word(q,at));assert!(k.c0.b.0==word(q,at+4));assert!(k.c1.a.0==word(q,at+8));assert!(k.c1.b.0==word(q,at+12));
  crate::fast_pairing::NBQ_advance(s);CALLS+=1;Ok(())
 }}
 fn finish(s:EbyKDot)->WideExact{unsafe{
  assert!(CALLS==3);assert!(crate::fast_pairing::NBQ_count(&s)==3);
  let limbs:[u32;8]=kani::any();
  for j in 0..8{kani::assume(limbs[j]<2147483647);OUTPUT[j]=limbs[j];}
  WideExact::from_limbs(limbs).unwrap()
 }}
 fn source(q:&[u8;608],g:&[WideExact;29],slot:usize,value:WideExact)->WideExact {
'''+cut+r'''
 }
 #[kani::proof] #[kani::unwind(608)]
 #[kani::stub(EbyKDot::push,push)] #[kani::stub(EbyKDot::finish,finish)]
 fn complete_tail(){
  let q:[u8;608]=kani::any();let slot:usize=kani::any();kani::assume(slot<4);
  for c in 0..3{let at=if c==0{slot*120+104}else{480+slot*32+(c-1)*16};for j in 0..4{kani::assume(word(&q,at+4*j)<2147483647);}}
  let mut g=[WideExact::ZERO;29];
  for i in 26..29{let raw:[u32;8]=kani::any();for j in 0..8{kani::assume(raw[j]<2147483647);}g[i]=WideExact::from_limbs(raw).unwrap();}
  let raw:[u32;8]=kani::any();for j in 0..8{kani::assume(raw[j]<2147483647);}let value=WideExact::from_limbs(raw).unwrap();
  unsafe{CALLS=0;DPTR=core::ptr::null_mut();GPTR=g.as_ptr();QPTR=q.as_ptr();SLOT=slot;}
  let out=source(&q,&g,slot,value).to_limbs();let j:usize=kani::any();kani::assume(j<8);
  unsafe{assert!(CALLS==3);assert!(u64::from(out[j])==(u64::from(raw[j])+u64::from(OUTPUT[j]))%2147483647);}
 }
}
'''
(E/'NBS_tail.patch').write_text(''.join(difflib.unified_diff(s.splitlines(True),(s+t).splitlines(True),fromfile='a/'+p,tofile='b/'+p)))
