from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdeac-20261028');N=D/'native02'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
log=(D/'native02-output.log').read_text()
expected='owned=[(1, 0, 4), (2, 4, 8), (2, 8, 74), (3, 69, 0)]\nborrowed=[(1, 0, 4), (2, 4, 8), (2, 8, 74)]\nvalue_bytes=74'
assert expected in log
assert "assert 'drop(_2)' in body" in log
mir=(N/'owned-join.mir').read_text();body=mir[mir.index('fn owned('):mir.index('fn borrowed(')]
assert 'Path::join::<String>(move _1, move _2)' in body
R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu')
lib=R/'lib/rustlib/src/rust/library'
s=(lib/'std/src/path.rs').read_text();a=s.index('pub fn join<P: AsRef<Path>>');a=s.rfind('\n',0,a)+1;b=s.index('\n    }',a)+6;join=s[a:b]
assert 'self._join(path.as_ref())' in join
out=dict(classification='finite native validation; no complete dispatch or endpoint claim',scope='native02',recovery='The optimized fixture completed with exit0 and both expected traces. The subsequent Python MIR check was wrong: ownership is transferred into the generic std join, rather than dropped in the caller MIR. Recovering the recorded run without recompiling or rerunning.',fixture_exit=0,scope_exit=1,stdout=expected,source_sha256=sha(D/'owned-join.rs'),binary_sha256=sha(N/'owned-join'),mir_sha256=sha(N/'owned-join.mir'),owned_wrapper=body,std_join=join,library_sources=[dict(path=str(p),sha256=sha(p)) for p in [lib/'std/src/path.rs',lib/'alloc/src/vec/mod.rs',lib/'alloc/src/raw_vec/mod.rs',lib/'alloc/src/string.rs']],toolchain='1.94.1; release opt3; debug_assertions=false overflow_checks=false panic=unwind',features='std-only fixture; project deployed feature graph inherited, no project body linked')
(N/'result.json').write_text(json.dumps(out,indent=2)+'\n');print('recovered successful native02 finite fixture without resubmission')
