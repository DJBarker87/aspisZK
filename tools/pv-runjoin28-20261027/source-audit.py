from pathlib import Path
import hashlib,subprocess,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin28-20261027'
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
rows=[]
for p in ['crates/aspis-statement/src/pool_v1/pair_forest_trace.rs','crates/aspis-statement/src/pool_v1/pair_trace.rs','crates/aspis-statement/src/pool_v1/payment_relation.rs','crates/aspis-statement/src/pool_v1/incremental_merkle.rs','crates/aspis-statement/src/pool_v1/pair_tree_profile.rs','crates/aspis-prover/src/pool_v1_pair_forest_honest.rs','crates/aspis-prover/src/v6_onefold_prover.rs']:
 b=(R/p).read_bytes();assert b==subprocess.check_output(['git','show','d73d800f26:'+p])
 rows.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest(),git_blob=subprocess.check_output(['git','rev-parse',rev+':'+p],text=True).strip()))
(E/'native-source-audit.json').write_text(json.dumps(dict(revision=rev,classification='source inspection, no execution/refinement inference',all_unchanged_from_entry=True,sources=rows),indent=2)+'\n')
print('Frozen compiler, validators, tree and caller sources unchanged')
