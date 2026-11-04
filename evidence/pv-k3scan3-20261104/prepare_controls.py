from pathlib import Path
import json
E=Path(__file__).resolve().parent;P=E/'caller'
p=P/'Cargo.toml';t=p.read_text().replace('context=[]','context=[]\n'+'\n'.join(f'mutation-{i}=[]' for i in range(12)));p.write_text(t)
p=P/'lib.rs';t=p.read_text();t+='\nfn mutation()->usize {\n'+''.join(f' if cfg!(feature="mutation-{i}") {{return {i};}}\n' for i in range(12))+' 0\n}\n'
t=t.replace('  check(x,y);','''  if cfg!(feature="negative-control") {
   let mode=crate::mutation();let limb=mode%4;
   let target=if mode<4 {&mut log.output[0]}else if mode<8 {&mut log.left[0]}else {&mut log.right[0]};
   match limb {0=>target.c0.a.0^=1,1=>target.c0.b.0^=1,2=>target.c1.a.0^=1,_=>target.c1.b.0^=1};
  }
  assert_eq!(x,y);''');p.write_text(t)
p=P/'array.rs';t=p.read_text().replace('assert_eq!(v.capacity(),usize::MAX);','assert_eq!(v.capacity(),if cfg!(feature="negative-control") && crate::mutation()==1 {0}else{usize::MAX});').replace('Ok(a)=>assert_eq!(a.len(),0),','Ok(a)=>assert_eq!(a.len(),if cfg!(feature="negative-control") && crate::mutation()==2 {1}else{0}),').replace('if cfg!(feature="negative-control") {log=1;}','if cfg!(feature="negative-control") && crate::mutation()==0 {log=1;}');p.write_text(t)
p=P/'context.rs';t=p.read_text().replace('let selectors=Selectors{high,low};','let mut selectors=Selectors{high,low};').replace('if cfg!(feature="negative-control") {log.events[log.used-1].reply.c0.a.0^=1;}','''if cfg!(feature="negative-control") {
  match crate::mutation() {
   0=>log.events[log.used-1].reply.c0.a.0^=1,
   1=>log.events[0].left.c0.a.0^=1,
   2=>log.events[0].right.c0.a.0^=1,
   3=>log.frame[0]^=1,
   4=>log.used-=1,
   _=>selectors.high[ranges[0].start].c0.a.0^=1,
  }
 }''');p.write_text(t)
p=P/'default.rs';t=p.read_text();a=t.index(' let expected=');z=t.index('\n assert_eq!(log.calls',a)
t=t[:a]+''' let mut expected=log.reply;let mut bytes=[0u8;64];let mut pos=0;
 if cfg!(feature="negative-control") {
  let mode=crate::mutation();
  if mode<8 {expected.0[mode]^=1;}else if mode==8 {bytes[0]=1;}else if mode==9 {bytes[63]=1;}else if mode==10 {pos=1;}else {log.frame[0]^=1;}
 }
 assert_eq!(core,expected);assert_eq!(buffer.pv_dl_bytes(),&bytes);assert_eq!(buffer.get_pos(),pos);'''+t[z:];p.write_text(t)
for ident,h,c in [(91920,'generic_default_gate::wrapper_default_arbitrary_core','C053'),(91921,'equivalence16::shared_repeat16','C156')]:
 (E/f'config-K{ident}.json').write_text(json.dumps({'harness':h,'credit':c,'negative':False},indent=2)+'\n')
controls=[('empty_gate::empty_noncopy_length_branches','C051',i,'') for i in [1,2]]
controls += [('generic_default_gate::wrapper_default_arbitrary_core','C053',i,'') for i in range(12)]
controls += [('equivalence16::shared_repeat16','C156',i,'') for i in range(12)]
controls += [(h,c,i,'context') for h,c in [('equivalence17::sum_high_nodes','C163'),('equivalence17::sum_high_path','C164')] for i in range(6)]
assert len(controls)==38
for i,(h,c,m,f) in enumerate(controls,91922):
 (E/f'config-K{i}.json').write_text(json.dumps({'harness':h,'credit':c,'negative':True,'features':','.join(filter(None,[f,f'mutation-{m}'])),'mutation':m},indent=2)+'\n')
(E/'CONTROL-PLAN.json').write_text(json.dumps({'ids':'K91922-K91959','count':38,'reason':'distinct argument/reply/frame or result corruptions; no unchanged positive regression','C051':'phantom Drop effect, wrong mismatch capacity, wrong zero-array length','C053':'eight core words, first/last buffer byte, cursor, frame','C156':'all four output/left-key/right-key limbs','C163_C164':'last reply, first left argument, first right argument, frame, call count, borrowed input frame'},indent=2)+'\n')
