#!/usr/bin/env python3
"""Scoped validation. Does not fetch, deploy, or replay the historical closure."""
import argparse, hashlib, json, os, signal, subprocess, sys, tempfile, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
OUT = REPO / 'results' / HERE.name

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def run(name, cmd, cwd, evidence, env=None, timeout=120):
    log = evidence / (name + '.log')
    start = time.monotonic()
    timed = ['/usr/bin/time', '-l' if sys.platform == 'darwin' else '-v', *cmd]
    peak = 0
    with log.open('w') as output:
        p = subprocess.Popen(timed, cwd=cwd, env=env, stdout=output,
                             stderr=subprocess.STDOUT, start_new_session=True)
        stopped = None
        while p.poll() is None:
            rows = subprocess.check_output(['ps','-axo','pid=,ppid=,rss='], text=True)
            table = [list(map(int,row.split())) for row in rows.splitlines() if row.strip()]
            owned = {p.pid}
            while True:
                expanded = owned | {pid for pid,ppid,rss in table if ppid in owned}
                if expanded == owned: break
                owned = expanded
            peak = max(peak,sum(rss for pid,ppid,rss in table if pid in owned))
            if peak > 7*1024*1024 or time.monotonic()-start > timeout:
                stopped = 'RESOURCE_OR_TIMEOUT'
                os.killpg(p.pid,signal.SIGKILL)
                break
            time.sleep(.1)
        code = p.wait()
    item = dict(name=name, command=timed, exit_code=code, wall_seconds=time.monotonic()-start,
                sampled_peak_tree_rss_kib=peak, status=stopped or ('PASS' if code==0 else 'FAIL'),
                log=log.name, log_sha256=sha(log))
    print(json.dumps(item),flush=True)
    return item

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--stage',choices=['python','rust','lean','semantic','all','kernel'],required=True)
    args=parser.parse_args()
    OUT.mkdir(parents=True,exist_ok=True)
    evidence=Path(tempfile.mkdtemp(prefix=args.stage+'-',dir=OUT))
    revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=REPO,text=True).strip()
    sources=list(HERE.rglob('*.lean'))+[HERE/'source_transcript.rs',HERE/'check.py',
        REPO/'crates/aspis-core/src/transcript.rs',REPO/'crates/aspis-core/src/circle.rs',
        REPO/'crates/aspis-core/src/field.rs',REPO/'crates/aspis-core/src/sumcheck.rs',
        REPO/'crates/aspis-core/src/statement_sumcheck.rs',REPO/'crates/aspis-core/src/state_only_sumcheck.rs',
        REPO/'docs/research/v8-no-work-100-20260907/experiments/performance_verifier.rs']
    report=dict(revision=revision,stage=args.stage,checks=[],
                sources={str(p.relative_to(REPO)):sha(p) for p in sources if '.lake' not in p.parts})
    with tempfile.TemporaryDirectory(prefix='aspis-completion-build-') as builddir:
        build=Path(builddir)
        def check(name,cmd,cwd=HERE,env=None):
            entry=run(name,cmd,cwd,evidence,env)
            report['checks'].append(entry)
            return entry['exit_code']==0
        if args.stage in ['python','all']:
            check('supplied-python',[sys.executable,'run.py','--stage','python'],HERE/'supplied')
            check('supplied-static',[sys.executable,'run.py','--stage','static'],HERE/'supplied')
        if args.stage in ['rust','all']:
            env=os.environ.copy();env['CARGO_TARGET_DIR']=str(build/'cargo')
            check('supplied-rust',['cargo','test','--release','--offline'],HERE/'supplied/rust',env)
            text=(REPO/'crates/aspis-core/src/sumcheck.rs').read_text()
            assert 'pub const SUMCHECK_COEFFICIENTS: usize = 7;' in text
            assert 'pub const SUMCHECK_BYTES: usize = SUMCHECK_COEFFICIENTS * 16;' in text
            if check('actual-source-compile',['rustc','--edition','2021','-O',str(HERE/'source_transcript.rs'),'-o',str(build/'source-transcript')]):
                check('actual-source-run',[str(build/'source-transcript')])
        if args.stage in ['lean','all']:
            lean=HERE/'lean'
            version=subprocess.check_output(['lake','env','lean','--version'],cwd=lean,text=True).strip()
            report['lean_version']=version
            assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
            env=os.environ.copy();env['LEAN_PATH']=str(build)
            for module in ['CausalPrograms','SourceSqueeze']:
                if not check(module,['lake','env','lean','-j1','-M2048','-o',str(build/(module+'.olean')),module+'.lean'],lean,env): break
                report.setdefault('fresh_first_party_artifacts',{})[module]=sha(build/(module+'.olean'))
            report['toolchain_imports']='Pinned Std/toolchain distribution reused; NOT source rebuilt'
            report['historical_aspis_closure']='NOT RUN; no historical Aspis first-party artifacts imported'
        if args.stage=='kernel':
            report['checks'].append(dict(name='fresh-kernel',status='NOT RUN',exit_code=2,
                reason='Use reviewed explicit-module command on capped Linux runner; never probe leanchecker --help'))
        if args.stage=='semantic':
            lean=HERE/'lean'
            env=os.environ.copy();env['LEAN_PATH']=str(build)
            version=subprocess.check_output(['lake','env','lean','--version'],cwd=lean,text=True).strip()
            assert '4.33.1' in version and '819816b2e0a3bf405af45ae5c7af2491d8f5bee6' in version
            report['lean_version']=version
            compiled=check('SemanticWireExecution',['lake','env','lean','-j1','-M2048','-o',str(build/'SemanticWireExecution.olean'),'SemanticWireExecution.lean'],lean,env)
            if compiled:
                report['fresh_first_party_artifacts']={'SemanticWireExecution':sha(build/'SemanticWireExecution.olean')}
                check('lean-semantic-fixtures',['lake','env','lean','-j1','-M2048','--run','SemanticFixtures.lean'],lean,env)
            if check('actual-source-compile',['rustc','--edition','2021','-O',str(HERE/'source_transcript.rs'),'-o',str(build/'source-transcript')]):
                check('actual-source-run',[str(build/'source-transcript')])
            def lines(name):
                path=evidence/name
                return [x for x in path.read_text().splitlines() if x.startswith(('SEMANTIC ','SEMANTIC_Q '))] if path.exists() else []
            a,b=lines('lean-semantic-fixtures.log'),lines('actual-source-run.log')
            okay=len(a)==64 and a==b
            report['checks'].append(dict(name='cross-language-semantic',exit_code=0 if okay else 1,
                status='PASS' if okay else 'FAIL',cases=len(a),scope='32 M31 and 32 full QM31 synthetic executions, actual selected Rust scalar kernel versus executable Lean; not complete payment acceptance'))
    report['status']='PASS_SCOPED_ONLY' if all(c['exit_code']==0 for c in report['checks']) else 'FAIL_OR_NOT_RUN'
    (evidence/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(evidence)
    return 0 if report['status']=='PASS_SCOPED_ONLY' else 2

if __name__=='__main__': raise SystemExit(main())
