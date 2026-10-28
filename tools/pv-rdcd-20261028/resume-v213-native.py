from pathlib import Path
import json,os,subprocess,hashlib,sys
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');P=D/'classification-project-fixture';O=D/'resume-v213-source';O.mkdir(exist_ok=True)
plans=json.load(open(D/'resume-extraction-plans.json'));original=plans['V213REF']['wrapper'];source=original+'''\nuse aspis_core::field::{M31,CM31,QM31,WideExact};
#[test]fn raw_constructor(){
 let words=[0,1,2,2147483646,2147483647,2147483648,u32::MAX];let mut count=0;
 fn q(w:[u32;4])->QM31{QM31{c0:CM31{a:M31(w[0]),b:M31(w[1])},c1:CM31{a:M31(w[2]),b:M31(w[3])}}}
 for a in words {for b in words {for c in words {for d in words {
 let x=q([a,b,c,d]);let y=q([d,c,b,a]);let n=WideExact::new(x,y);let r=owned_wide_new::new(x,y);
 assert_eq!(n.c0(),r.c0);assert_eq!(n.c1(),r.c1);count+=1;
 }}}}
 println!("V213 {count} raw constructor pairs, every coordinate at zero/P/overflow boundaries; finite validation");
}
'''
(P/'fixture.rs').write_text(source)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_TARGET_DIR=str(D/'classification-target'),CARGO_BUILD_JOBS='4')
cmd=['cargo','test','--manifest-path',str(P/'Cargo.toml'),'--release','--offline','--locked','-j','4','--lib','raw_constructor','--','--nocapture','--test-threads=1']
m=json.loads(subprocess.check_output(['cargo','metadata','--manifest-path',str(P/'Cargo.toml'),'--offline','--locked','--format-version','1'],env=env,text=True));nodes={p['id']:p for p in m['resolve']['nodes']}
(O/'native-inputs.json').write_text(json.dumps(dict(command=cmd,toolchain=subprocess.check_output(['rustc','-vV'],env=env,text=True),features=[dict(name=p['name'],version=p['version'],features=nodes[p['id']]['features']) for p in m['packages']],profile='release opt3 debug_assertions=false overflow_checks=false',compiled_fixture_sha256=hashlib.sha256(source.encode()).hexdigest(),fixture=source,reason='arbitrary raw QM31 constructor inputs; no reduction to canonical-input domain; finite validation only, not Kani or source proof'),indent=2)+'\n')
print('Expected time: optimized cached compilation then2401 paired raw constructor checks',flush=True)
sys.exit(subprocess.run(cmd,env=env).returncode)
