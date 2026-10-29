from pathlib import Path
import subprocess,json,hashlib,re,tomllib
D=Path('/home/dombarker/project-offloads/codex-pv-diag2-20261029');T=D.parent/'codex-pv-rdea-20261028/client-target/release/deps';lib=next(T.glob('liblog-*.rlib'));src=D/'PV_DIAG2_LogGuard.rs';exe=D/'log-guard';rustc='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/bin/rustc';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cmd=[rustc,'--edition=2021','-C','opt-level=3','-C','debug-assertions=no','-C','overflow-checks=no','-C','panic=unwind','--extern','log='+str(lib),'-L','dependency='+str(T),str(src),'-o',str(exe)]
print('Expected time: optimized facade-guard probe compilation and ten finite controls',flush=True);subprocess.run(cmd,check=True);r=subprocess.run([str(exe)],capture_output=True,text=True);assert r.returncode==0
root=Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
def body(p,needle):
 text=p.read_text();m=re.search(r'(?m)^[ \t]*'+re.escape(needle),text);assert m;a=m.start();j=text.index('{',a);k=j+1;depth=1
 while depth:depth+=(text[k]=='{')-(text[k]=='}');k+=1
 return text[a:k]
parity=[]
for file,needle in [('macros.rs','macro_rules! __log'),('lib.rs','pub fn max_level()'),('lib.rs','pub const STATIC_MAX_LEVEL:')]:
 a=root/'log-0.4.33/src'/file;b=root/'log-0.4.34/src'/file;left=body(a,needle);right=body(b,needle);assert left==right
 parity.append(dict(needle=needle,old_source=str(a),old_sha256=sha(a),deployed_source=str(b),deployed_sha256=sha(b),complete_body_sha256=hashlib.sha256(right.encode()).hexdigest(),byte_identical=True))
lock=D.parent/'codex-pv-fscan-20261028/src/tools/r1-cost-probe/Cargo.lock';packages=tomllib.loads(lock.read_text())['package'];assert any(p['name']=='log' and p['version']=='0.4.34' for p in packages)
out=dict(deployed_lock=str(lock),deployed_lock_sha256=sha(lock),body_parity=parity,depinfo_sha256=sha(lib.with_name(lib.name[3:]).with_suffix('.d')),classification='finite deployed log facade validation; not proof of native dependency logger/filter configuration stability',command=cmd,rlib_sha256=sha(lib),source_sha256=sha(src),toolchain=subprocess.check_output([rustc,'-vV'],text=True),features='log0.4.34 features[]; exact release rlib reused',results=json.loads(r.stdout),open='arbitrary native dependencies may set_max_level/install logger or log directly; current filter/public-state closure remains P')
(D/'log-guard-validation.json').write_text(json.dumps(out,indent=2)+'\n');print(r.stdout)
