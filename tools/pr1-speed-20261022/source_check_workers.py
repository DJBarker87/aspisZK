from pathlib import Path
import subprocess,re,json,hashlib
r=Path(__file__).resolve().parents[2];base='ac5c20c4c5';z='docs/research/v8-r0-zk-20261009/z4/';c='docs/research/v8-r0-zk-20261009/c3/'
def old(p):return subprocess.check_output(['git','show',base+':'+p],text=True)
def body(s,name):
 a=s.index('fn '+name+'(');a=s.index('{',a);b=a+1;d=1
 while d:d+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a:b]
def norm(s):return re.sub(r'\s+','',s)
for path,funcs in [(c+'check/src/lib.rs',['ents_ok','prod_ok']),(c+'build/src/lib.rs',['fill_own','fill_rel','fill_round','fill_gbat'])]:
 for f in funcs:
  before=body(old(path),f);after=body((r/path).read_text(),f)
  anchor='    let mut ok = true;' if '/check/' in path else '    let mut out:'
  # Worker dispatch precedes the original scalar function body verbatim.
  assert norm(before)==norm('{\n'+after[after.index(anchor):]),f
before=body(old(z+'z9c.rs'),'emit');current=(r/(z+'z9c.rs')).read_text()
outer=body(current,'emit');assert outer.index('for m in lift_members(0)') < outer.index('ordered_families(3')
assert 'if first.rank()<w' in outer and 'first.insert(lift_src(&p.cx,0,m))' in outer
# Every elimination/pivot/early-exit statement is retained inside each family.
lift=before[before.index('    let mut tt = Instant::now();'):before.index('    info.t_lifts = tt.elapsed().as_secs_f64();')].replace('let mut tt','let tt').replace('return (None, info);','return None;')+'    info.t_lifts = tt.elapsed().as_secs_f64();\n    Some(lifts)\n'
assert norm(body(current,'emit_lifts'))==norm('{'+lift+'}')
q=before[before.index('    let targets ='):before.index('    // BCondG:')].rsplit('    tt = Instant::now();',1)[0].replace('return (None, info);','return None;')
q=q.replace('targets.iter().map(|b| rech.express(b.clone())).collect()','aspis_r1_cert_check::native_workers::ordered_map(targets.len(), |i| rech.express(targets[i].clone())).into_iter().collect()')
assert norm(body(current,'emit_qprime'))==norm('{let a=&p.a;let tt=Instant::now();'+q+'Some((kept,qp_y))}')
b=before[before.index('    // BCondG:'):before.index('    if p.qs.len() > 22')].replace('return (None, info);','return None;')
b=b.replace('nvec.iter().map(|n| vech.express(n.clone())).collect()','aspis_r1_cert_check::native_workers::ordered_map(nvec.len(), |i| vech.express(nvec[i].clone())).into_iter().collect()')
assert norm(body(current,'emit_bcond'))==norm('{let tt=Instant::now();'+b+'Some((bc_u,bc_piv,bc_fr,gk,bc_y))}')
for f in ['public_data','extracted_builders','p_r1_check']:
 assert body(old(z+'z9e.rs'),f)==body((r/(z+'z9e.rs')).read_text(),f),f
assert (r/(c+'check/src/native_workers.rs')).read_bytes()==(r/'tools/pr1-speed-20261022/worker-template.rs.txt').read_bytes()
assert not subprocess.check_output(['git','diff',base,'--name-only','--','crates','programs'],text=True).strip()
paths=[c+'check/src/native_workers.rs',c+'check/src/lib.rs',c+'build/src/lib.rs',z+'z9c.rs',z+'z9d.rs',z+'z9e.rs','Cargo.lock',z+'Cargo.lock']
print(json.dumps(dict(stage2=base,checks=['original scalar checker/builder bodies retained','emitter family elimination/pivot statements identical','only target-row scheduling changed inside emitter families','public_data/extracted_builders/P_R1 catch boundary unchanged','worker source matches template','crates/programs unchanged'],source_sha256={p:hashlib.sha256((r/p).read_bytes()).hexdigest()for p in paths},trust='Independent pure public callbacks, ordered contiguous partition, join-before-resume; std/OS/allocator trusted. Partition Kani plus source composition, not a whole-program concurrency proof.'),indent=2))
