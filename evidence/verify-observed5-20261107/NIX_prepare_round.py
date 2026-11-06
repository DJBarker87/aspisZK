from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
n='crates/aspis-r1-cost-probe/src/r1_semantic.rs';s=subprocess.check_output(['git','show','4bb3b3f5:'+n],text=True)
head='fn semantic_round<H: Digest32>(prefix: &Prefix<\'_>, mut transcript: SemanticTranscript<H>, mut alpha: [QM31; 10], mut running: QM31, round: usize) -> Result<(QM31, [QM31; 10], SemanticTranscript<H>), Error> {'
b=s.split(head,1)[1].split('\n}',1)[0]
repls=[('prefix.validated_record(row)?.decode_k::<28>(0)?','decode(prefix.validated_record(row)?,0,polyreply,log)?'),('semantic_boundary(&polynomial)','boundary(&polynomial,boundaryreply,k,log)'),('transcript.semantic_validated(prefix.validated_record(row)?)?','semantic(&mut transcript,prefix.validated_record(row)?,semreply,newstate,newnext,log)?'),('semantic_value(&polynomial, &alpha, round)','value(&polynomial,&alpha,round,valuereply,k,j,log)')]
cut=b
for a,c in repls:assert cut.count(a)==1;cut=cut.replace(a,c)
mod='''
#[cfg(kani)] pub mod NIX_round {
 use super::*;use crate::r1_wire::ValidatedRecord;
 fn same(a:QM31,b:QM31)->bool{a.c0.a.0==b.c0.a.0&&a.c0.b.0==b.c0.b.0&&a.c1.a.0==b.c1.a.0&&a.c1.b.0==b.c1.b.0}
 struct Log{decode_row:u8,ptr:*const u8,len:usize,offset:usize,bp:QM31,vp:QM31,va:QM31,value_round:usize,semantic_row:u8,semantic_ptr:*const u8,semantic_len:usize,state:[u8;32],next:u8,times:[u8;4],count:u8,frame:u64}
 fn tick(i:usize,l:&mut Log){l.times[i]=l.count;l.count+=1;}
 fn decode(record:ValidatedRecord<'_>,offset:usize,reply:Result<[QM31;28],Error>,l:&mut Log)->Result<[QM31;28],Error>{l.decode_row=record.row();l.ptr=record.framed().as_ptr();l.len=record.framed().len();l.offset=offset;tick(0,l);reply}
 fn boundary(poly:&[QM31;28],reply:QM31,k:usize,l:&mut Log)->QM31{l.bp=poly[k];tick(1,l);reply}
 fn semantic<H:Digest32>(t:&mut SemanticTranscript<H>,r:ValidatedRecord<'_>,reply:Result<QM31,Error>,state:[u8;32],next:u8,l:&mut Log)->Result<QM31,Error>{l.semantic_row=r.row();l.semantic_ptr=r.framed().as_ptr();l.semantic_len=r.framed().len();l.state=t.state();l.next=t.next_row();tick(2,l);crate::r1_wire::NIX_round_constructor::update(t,state,next);reply}
 fn value(poly:&[QM31;28],alpha:&[QM31;10],round:usize,reply:QM31,k:usize,j:usize,l:&mut Log)->QM31{l.vp=poly[k];l.va=alpha[j];l.value_round=round;tick(3,l);reply}
 fn step<H:Digest32>(prefix:&Prefix<'_>,mut transcript:SemanticTranscript<H>,mut alpha:[QM31;10],mut running:QM31,round:usize,polyreply:Result<[QM31;28],Error>,boundaryreply:QM31,semreply:Result<QM31,Error>,newstate:[u8;32],newnext:u8,valuereply:QM31,k:usize,j:usize,log:&mut Log)->Result<(QM31,[QM31;10],SemanticTranscript<H>),Error>{BODY
 }
 pub fn check<H:Digest32>(hash:H,negative:bool){
  let bytes:[[u8;3717];27]=kani::any();let sizes:[usize;27]=kani::any();for size in sizes {kani::assume(size<=3717);}
  let records:[&[u8];27]=core::array::from_fn(|i| &bytes[i][..sizes[i]]);let root:[u8;32]=kani::any();let prefix=crate::r1_wire::NIX_round_constructor::prefix(&root,records);
  let round:usize=kani::any();kani::assume(round<10);let row=15+round as u8;let k:usize=kani::any();kani::assume(k<28);let j:usize=kani::any();kani::assume(j<10);let z:usize=kani::any();kani::assume(z<32);
  let alpha:[QM31;10]=kani::any();let running:QM31=kani::any();let poly:[QM31;28]=kani::any();let bd:QM31=kani::any();let challenge:QM31=kani::any();let value:QM31=kani::any();let decode_ok:bool=kani::any();let semantic_ok:bool=kani::any();let bad_value:usize=kani::any();kani::assume(bad_value<28);let e:u8=kani::any();let a:u8=kani::any();let tag:u8=kani::any();kani::assume(tag<2);
  let polyreply=if decode_ok{Ok(poly)}else{Err(if tag==0{Error::Length{row}}else{Error::NonCanonical{row,value:bad_value}})};let semreply=if semantic_ok{Ok(challenge)}else{Err(Error::RowOrder{expected:e,actual:a})};
  let state:[u8;32]=kani::any();let next:u8=kani::any();let newstate:[u8;32]=kani::any();let newnext:u8=kani::any();let count:u8=kani::any();kani::assume(count<252);let frame:u64=kani::any();let seed:QM31=kani::any();let times:[u8;4]=kani::any();let oldstate:[u8;32]=kani::any();
  let mut l=Log{decode_row:0,ptr:core::ptr::null(),len:0,offset:99,bp:seed,vp:seed,va:seed,value_round:99,semantic_row:0,semantic_ptr:core::ptr::null(),semantic_len:0,state:oldstate,next:0,times,count,frame};
  let t=crate::r1_wire::NIX_round_constructor::transcript(hash,state,next);let mut out=step(&prefix,t,alpha,running,round,polyreply,bd,semreply,newstate,newnext,value,k,j,&mut l);
  if negative {out=Err(Error::Terminal);}
  assert_eq!(l.decode_row,row);assert_eq!(l.ptr,records[row as usize].as_ptr());assert_eq!(l.len,sizes[row as usize]);assert_eq!(l.offset,0);assert_eq!(l.times[0],count);assert_eq!(l.frame,frame);
  let boundary_ok=same(bd,running);let has_semantic=decode_ok&&boundary_ok;let has_value=has_semantic&&semantic_ok;
  if decode_ok{assert!(same(l.bp,poly[k]));assert_eq!(l.times[1],count+1);}else{assert!(same(l.bp,seed));assert_eq!(l.times[1],times[1]);}
  if has_semantic{assert_eq!(l.semantic_row,row);assert_eq!(l.semantic_ptr,records[row as usize].as_ptr());assert_eq!(l.semantic_len,sizes[row as usize]);assert_eq!(l.state[z],state[z]);assert_eq!(l.next,next);assert_eq!(l.times[2],count+2);}else{assert_eq!(l.semantic_row,0);assert!(l.semantic_ptr.is_null());assert_eq!(l.semantic_len,0);assert_eq!(l.state[z],oldstate[z]);assert_eq!(l.next,0);assert_eq!(l.times[2],times[2]);}
  if has_value{assert!(same(l.vp,poly[k]));assert!(same(l.va,if j==round{challenge}else{alpha[j]}));assert_eq!(l.value_round,round);assert_eq!(l.times[3],count+3);}else{assert!(same(l.vp,seed)&&same(l.va,seed));assert_eq!(l.value_round,99);assert_eq!(l.times[3],times[3]);}
  assert_eq!(l.count,count+if !decode_ok{1}else if !boundary_ok{2}else if !semantic_ok{3}else{4});
  match out{Ok((r,al,t))=>{assert!(has_value);assert!(same(r,value));assert!(same(al[j],if j==round{challenge}else{alpha[j]}));assert_eq!(t.state()[z],newstate[z]);assert_eq!(t.next_row(),newnext);},Err(err)=>{if !decode_ok{if tag==0{assert!(matches!(err,Error::Length{row:r} if r==row));}else{assert!(matches!(err,Error::NonCanonical{row:r,value:v} if r==row&&v==bad_value));}}else if !boundary_ok{assert!(matches!(err,Error::Boundary{round:r} if r==round));}else{assert!(!semantic_ok);assert!(matches!(err,Error::RowOrder{expected:x,actual:y} if x==e&&y==a));}}}
 }
}
'''.replace('BODY',cut)
p=E/'NIX_src'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s+mod);(E/'NIX_round.rs.txt').write_text(mod)
nwire='crates/aspis-r1-cost-probe/src/r1_wire.rs';p=E/'NIX_src'/nwire;ws=p.read_text();ws+='''
#[cfg(kani)] pub mod NIX_round_constructor {
 use super::*;
 pub fn transcript<H:Digest32>(hash:H,state:[u8;32],next_row:u8)->SemanticTranscript<H>{SemanticTranscript{hash,state,next_row}}
 pub fn update<H:Digest32>(t:&mut SemanticTranscript<H>,state:[u8;32],next_row:u8){t.state=state;t.next_row=next_row;}
 pub fn prefix<'a>(c1_root:&'a[u8;32],records:[&'a[u8];27])->Prefix<'a>{Prefix{c1_root,records}}
}
''';p.write_text(ws)
np='programs/r1-cost-probe/src/lib.rs';p=E/'NIX_src'/np;s=p.read_text()+'''
#[cfg(kani)] mod NIX_round_program {
 #[kani::proof] #[kani::unwind(3720)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NIX_kmx::KMX_copy_nonoverlapping)] fn native(){aspis_r1_cost_probe::r1_semantic::NIX_round::check(super::SolanaDigest,false);}
 #[kani::proof] #[kani::unwind(3720)] #[kani::stub(core::ptr::copy_nonoverlapping,crate::NIX_kmx::KMX_copy_nonoverlapping)] fn control(){aspis_r1_cost_probe::r1_semantic::NIX_round::check(super::SolanaDigest,true);}
}
''';p.write_text(s)
pins=json.loads((E/'NIX_SOURCE_PINS.json').read_text())
for name in [n,nwire,np]:pins[name]=hashlib.sha256((E/'NIX_src'/name).read_bytes()).hexdigest()
(E/'NIX_SOURCE_PINS.json').write_text(json.dumps(pins));(E/'NIX_ROUND_ERASURE.json').write_text(json.dumps(dict(frozen_body_sha256=hashlib.sha256(b.encode()).hexdigest(),cut_body_sha256=hashlib.sha256(cut.encode()).hexdigest(),replacements=repls,scope='deployed prover absent; actual SolanaDigest; no field products',domain='all Prefix records independently arbitrary length<=3717; 0<=round<10; no parsed-prefix/success restriction'),indent=2)+'\n')
x=json.loads((E/'NIX_L056.json').read_text());x.update(attempt='NIX_L066',module='Install round133 cut and explicit cfg(kani) native constructors',sources=['NIX_src/'+a for a in [n,nwire,np]]+['NIX_SOURCE_PINS.json','NIX_ROUND_ERASURE.json'],command=['python3','-c','import json;print(json.load(open("NIX_ROUND_ERASURE.json")))']);(E/'NIX_L066.json').write_text(json.dumps(x,indent=2))
for i,hn in [(60,'native'),(61,'control')]:
 a=f'NIX_K{i:03}';x=json.loads((E/'NIX_K049.json').read_text());x.update(attempt=a,module='NIX_round_program::'+hn);x['command'][2]=a+'.json';idx=x['native_command'].index('--harness');x['native_command'][idx+1]=x['module'];x['collect']=[a+s for s in ['-graph-check.json','-graph.stderr','-graph.json','-source-check.json','-lock-check.json']];x['expected_time']='optimized compile then native single round with arbitrary Prefix/alpha/transcript; only opaque scalar/record callees';(E/(a+'.json')).write_text(json.dumps(x,indent=2))
