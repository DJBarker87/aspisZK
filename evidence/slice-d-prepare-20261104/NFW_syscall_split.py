from pathlib import Path
import json,hashlib,difflib
E=Path(__file__).resolve().parent;C='programs/r1-cost-probe/src/';p=E/'NFW_syscall.rs.txt';old=p.read_text();s=old
s=s.replace('bytes:[u8;5],positions:[usize;5]','observed:u8,position:usize,selected:usize')
s=s.replace('let j=log.positions[i];log.bytes[i]=if j<xs[i].len(){xs[i][j]}else{0};','')
s=s.replace('i+=1;}Hash::new_from_array(log.reply)','i+=1;}let j=log.position;let target=xs[log.selected];log.observed=if j<target.len(){target[j]}else{0};Hash::new_from_array(log.reply)')
s=s.replace('let count:usize=kani::any();kani::assume(count<=5);','let count:usize=kani::any();kani::assume(count<=5);let selected=if cfg!(NFW_part0){0}else if cfg!(NFW_part1){1}else if cfg!(NFW_part2){2}else if cfg!(NFW_part3){3}else{4};kani::assume(selected<count);')
s=s.replace('bytes:[0;5],positions:kani::any()','observed:0,position:kani::any(),selected')
s=s.replace('let part:usize=kani::any();kani::assume(part<count);assert_eq!(log.lengths[part],lengths[part]);let at=log.positions[part];','let part=selected;assert_eq!(log.lengths[part],lengths[part]);let at=log.position;')
s=s.replace('log.bytes[part]==expected','log.observed==expected')
p.write_text(s);x=json.loads((E/'NFW_NATIVE_INPUTS.json').read_text());x[C+'NFW_syscall.rs']=s;(E/'NFW_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n')
x=json.loads((E/'NFW_SOURCE_PINS.json').read_text());x[C+'NFW_syscall.rs']=hashlib.sha256(s.encode()).hexdigest();(E/'NFW_SOURCE_PINS.json').write_text(json.dumps(x,indent=1)+'\n')
(E/'NFW_syscall_split.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/NFW_syscall.rs',tofile='b/NFW_syscall.rs')))
p=E/'NFW_run.py';s=p.read_text();needle="if os.environ.get('NFW_BADARG'):env['RUSTFLAGS']+=' --cfg NFW_badarg'";s=s.replace(needle,needle+"\n if os.environ.get('NFW_PART') is not None:\n  part=int(os.environ['NFW_PART']);assert 0<=part<5;env['RUSTFLAGS']+=' --cfg NFW_part'+str(part)");p.write_text(s)
(E/'NFW_K019_REVIEW.json').write_text(json.dumps(dict(attempt='NFW_K019',disposition='TIMEOUT; zero credit',wall_seconds=93.23956078896299,peak_rss_kib=6354164,swaps=0,replacement='Per-part selected byte only; other part byte observations eliminated, exact length/return frame retained; original harness name; no cap/time increase'),indent=1)+'\n')
