"""Pinned source/control-flow audit; no native reachability or privacy claim."""
from pathlib import Path
import subprocess,json,hashlib,re
E=Path('evidence/pv-fib-20261029');rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();records=[]
def read(path):
 b=subprocess.check_output(['git','show',rev+':'+path]);records.append(dict(path=path,revision=rev,sha256=hashlib.sha256(b).hexdigest(),git_blob=subprocess.check_output(['git','rev-parse',rev+':'+path],text=True).strip(),bytes=len(b)));return b.decode()
p=read('tools/r1-cost-probe/src/bin/devnet_spend/plan.rs');m=read('tools/r1-cost-probe/src/bin/devnet_spend.rs')
prover=read('crates/aspis-r1-cost-probe/src/prover.rs');read('crates/aspis-r1-cost-probe/src/RealR1_client.rs');read('crates/aspis-prover/src/state_only_entropy.rs');read('tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs')
runtime=read('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_Deployed.lean');retry=read('docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_UnifiedRetry.lean')
headline=read('docs/research/v8-r0-zk-20261009/lean/R1Z/PrivacyR1HeadlineDeployedReal.lean');bad=read('docs/research/v8-r0-zk-20261009/lean/R1Z/QueryScanRealLazyBound.lean');fuel=read('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitFuelJoin22.lean');seed=read('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitSeedEvent19.lean')
checks={
 'deployed_feature_arm': '#[cfg(feature="r1p-check")]' in p[:p.index('let started=Instant::now()')][-600:],
 'one_start_one_elapsed':p.count('Instant::now()')==p.count('started.elapsed()')==1,
 'elapsed_after_return_and_files':p.index('let result=RealR1_client::prove_for_proof_accounts')<p.index('fs::write(dir.join("proof.bin")')<p.index('"prove_wall_seconds":started.elapsed().as_secs_f64()'),
 'start_used_only_for_elapsed':len(re.findall(r'\bstarted\b',p))==2,
 'stdout_uses_returned_json':'println!("{}",plan::run(&q)?)' in m,
 'core_result_has_no_clock':'Result (Output N L C) → View' in runtime and 'Instant' not in runtime and 'elapsed' not in retry,
 'exact_headline_old':'QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w' in headline,
 'exact_headline_queries':'(realSeedQueries template outputs x rust observer_program adv w)' in headline,
 'parser_only_realBad':'parserBad (fun j => attVec' in bad,
 'only_rejected_retries':'Err(Error::Rejected)=>retry_attempt' in prover and 'Err(e)=>Err(e)' in prover,
 'retry_causes_present':all(s in prover for s in ['StateOnlyMaskBuildError::MaskSampleExhausted','SError::ActivePole','if accepted {Ok(())} else {Err(Error::Rejected)}']),
 'good_events_no_wall_clock':all(s not in bad+fuel+seed for s in ['Instant','elapsed','prove_wall_seconds']),
}
assert all(checks.values()),checks
# Check exact current deployed wrapper against the retained client build source.
historical=subprocess.check_output(['git','show',rev+':evidence/pv-client-20261026/build-03/sources/src/tools/r1-cost-probe/src/bin/devnet_spend/plan.rs']).decode()
checks['deployed_wrapper_equals_client_build03']=historical==p
# This is reported even if later legitimate source edits changed the full wrapper.
(E/'source-check.json').write_text(json.dumps(dict(checks=checks,sources=records,
 evidence_class='source/control-flow counterexample: post-result clock-read influence',
 limitation='No native paired execution, no sampled-coins off-bad certificate, no actual-body termination proof. The formal clock obstruction is conditional on one non-bad completed path; native scheduling/source association stays explicit.'),indent=2)+'\n')
print(json.dumps(checks,indent=2))
