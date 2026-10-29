from pathlib import Path
import subprocess,json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2e-20261029'
paths=['crates/aspis-r1-cost-probe/src/'+x for x in ['lib.rs','sampler.rs','host_sampler.rs','transcript.rs','host_transcript.rs','prover.rs','verifier.rs','dense.rs']]
rows=[]
for p in paths:
 raw=subprocess.check_output(['git','show','HEAD:'+p]);s=raw.decode();hits=[]
 for i,line in enumerate(s.splitlines(),1):
  if any(w in line for w in ['gamma_sample','ordinary_sample','transcript::Transcript','host_transcript::Transcript','pub mod sampler','pub mod transcript','mod host_sampler','mod host_transcript']):hits.append(dict(line=i,text=line))
 rows.append(dict(path=p,source_sha256=hashlib.sha256(raw).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+p],text=True).strip(),sites=hits))
lib=subprocess.check_output(['git','show','HEAD:'+paths[0]],text=True);assert 'pub mod sampler;'in lib and '#[cfg(feature="prover")] mod host_sampler;'in lib
ver=subprocess.check_output(['git','show','HEAD:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True);assert 'transcript::Transcript' in ver and 'host_transcript::Transcript'not in ver
pro=subprocess.check_output(['git','show','HEAD:crates/aspis-r1-cost-probe/src/prover.rs'],text=True);assert 'host_transcript::Transcript'in pro
r=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),rows=rows,deployed_features=['r1p-check','aspis-r1-cost-probe/ct-host-prover'],profile='release',toolchain='rustc1.94.1',original_route='verifier.rs uses transcript::Transcript::scalar → sampler::{gamma_sample,ordinary_sample}; original iterator/from_fn body. Both branches traced by nonzero bool.',host_route='prover.rs uses host_transcript::Transcript::scalar → host_sampler::{gamma_sample,ordinary_sample}; dense.rs also calls host_sampler. Indexed source is distinct.',proof_credit='source inventory and exact caller distinction; not an assertion of runtime reachability of every call in the complete deployment',remaining='universal original raw mutable references/array construction → offset/current-store model and actual consuming verifier call law; do not substitute host callback merely because outputs agree on finite inputs')
(E/'deployed-call-sites.json').write_text(json.dumps(r,indent=2));print('PASS source aliases distinguished; original verifier and indexed prover routes retained')
