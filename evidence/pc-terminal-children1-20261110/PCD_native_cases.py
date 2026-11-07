from pathlib import Path
import json,subprocess,sys,lzma,re
E=Path(__file__).resolve().parent
ids=json.loads((E/'PCD_NATIVE_CASE_IDS.json').read_text())['available'][:24]
groups=[[0,1,2]]+[[i] for i in range(3,14)]
plan=[]
for number,tags in enumerate(groups):
 for negative,a in enumerate(ids[2*number:2*number+2]):
  plan.append(dict(attempt=f'PCD_K{a:03d}',tags=tags,negative=bool(negative),harness='PCD_box_corrupt_control' if negative and number==0 else 'PCD_box_value_control' if negative else 'PCD_box_contract'))
(E/'PCD_NATIVE_CASE_PLAN.json').write_text(json.dumps({'kind':'partition of the original 14-tag value observation domain; no harness rename','groups':groups,'steps':plan},indent=1)+'\n')
for tags in groups:
 f=E/'PCD_box_native.rs';source=f.read_text();a=source.index('    fn PCD_box_contract()');b=source.index('\n    #[kani::proof]',a)
 tag='let tag:u8=kani::any();kani::assume(tag<3);' if len(tags)>1 else f'let tag:u8={tags[0]};'
 body='''    fn PCD_box_contract() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();
        TAG
        let i:u8=kani::any();let j:u8=kani::any();kani::assume(i<8&&j<32);
        let _=PCD_box_segment(&value,&mut log,tag,i as usize,j as usize,0);
    }
'''.replace('TAG',tag)
 source=source[:a]+body+source[b:]
 if '\n    // PCD VALUE CASE CONTROL\n' in source:source=source[:source.index('\n    // PCD VALUE CASE CONTROL\n')]
 source+='''
    // PCD VALUE CASE CONTROL
    #[kani::proof]
    #[kani::stub(core::ptr::copy_nonoverlapping,kmx::KMX_copy_nonoverlapping)]
    fn PCD_box_value_control() {
        let value=PCD_request_value();let mut log=PCD_BoxLog::default();
        TAG
        let i:u8=kani::any();let j:u8=kani::any();kani::assume(i<8&&j<32);
        let out=PCD_box_body(&value,&mut log);
        assert!(PCD_request_observe(&out,tag,i as usize,j as usize)!=PCD_request_observe(&value,tag,i as usize,j as usize));
    }
'''.replace('TAG',tag)
 f.write_text(source)
 prep=subprocess.run([sys.executable,str(E/'PCD_prepare_frontier.py')],capture_output=True,text=True);assert prep.returncode==0,prep.stderr
 for item in [q for q in plan if q['tags']==tags]:
  a=item['attempt'];r=subprocess.run([sys.executable,str(E/'PCD_native_run.py'),a],capture_output=True,text=True)
  file=E/a/'stdout.log.xz'
  if not file.exists():print(a+' no scope receipt: '+(r.stdout+r.stderr)[-300:],flush=True);sys.exit(1)
  text=lzma.decompress(file.read_bytes()).decode();timeout='CBMC timed out' in text
  positive='VERIFICATION:- SUCCESSFUL' in text
  m=re.search(r'Failed Checks: ([^\n]+)',text)
  negative='VERIFICATION:- FAILED' in text and m is not None and not timeout and 'unwinding assertion' not in text
  verdict='PASS' if positive else 'TIMEOUT' if timeout else 'FAIL '+m[1] if m else 'NO_SEMANTIC_VERDICT'
  with (E/'PCD_NATIVE_CASE_VERDICTS.jsonl').open('a') as out:out.write(json.dumps(dict(**item,verdict=verdict,scope_exit=r.returncode))+'\n')
  print(a+' tags='+str(tags)+' '+verdict[:160],flush=True)
  if (item['negative'] and not negative) or (not item['negative'] and not positive):
   # A timed-out case gives no credit, and is never rerun. Independent cases may proceed.
   if not timeout:sys.exit(1)
