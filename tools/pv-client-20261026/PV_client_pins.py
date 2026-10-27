#!/usr/bin/env python3
"""Pin a conservative source/dependency superset and the operational entry chain."""
import argparse,hashlib,json,pathlib,subprocess
ROOT=pathlib.Path(__file__).resolve().parents[2]
E=ROOT/'evidence/pv-client-20261026'
ROUTES=[
 ('scripts/r1_devnet_spend.py','p,proofkey=proof_plan(', 'Python operational orchestration, including manifest/errors/publication/events'),
 ('scripts/Client64_proof_accounts.py','def proof_plan(', 'retained keys, exclusive claim and durable resume state'),
 ('scripts/Client64_proof_accounts.py','plan = invoke(request)', 'enters the configured pinned runner'),
 ('scripts/r1_devnet_spend.py','def invoke(', 'subprocess boundary to devnet_spend'),
 ('tools/r1-cost-probe/src/bin/devnet_spend.rs','fn main()', 'Rust entry: action=prove JSON branch; include signing/errors in complete client experiment'),
 ('tools/r1-cost-probe/src/bin/devnet_spend.rs','plan::run(&q)?', 'dispatch'),
 ('tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','pub fn run(', 'planner dispatch'),
 ('tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','fn prove(q:', 'operational selected64 prover entry'),
 ('tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','RealR1_client::prove_for_proof_accounts(', 'selected adapter call with concrete ordered retained-key callback'),
 ('crates/aspis-r1-cost-probe/src/RealR1_client.rs','pub fn prove_for_proof_accounts(', 'S2, eight attempts, 64 private bytes, public nonce = proof-account key'),
 ('crates/aspis-r1-cost-probe/src/RealR1_client.rs','StateOnlyAttemptSecrets::generate_for_mask_nonce(', 'selected entropy callback'),
 ('crates/aspis-r1-cost-probe/src/prover.rs','pub fn prove_masked_retrying_with(', 'retry owner; only Rejected retries'),
 ('crates/aspis-r1-cost-probe/src/prover.rs','pub fn prove_masked_attempt(', 'public serialization/hash and context before reserve/body'),
 ('crates/aspis-r1-cost-probe/src/prover.rs','fn prove_masked_with_attempt(', 'reservation and complete private body'),
 ('crates/aspis-prover/src/state_only_entropy.rs','pub fn reserve_and_build_pool_v1_pair_forest_mask_material_v1(', 'durable nonce reservation before secret derivation'),
 ('crates/aspis-r1-cost-probe/src/prover.rs','fn prove_from_semantics(', 'remaining prover body'),
]
ROOTS=['Cargo.toml','Cargo.lock','.cargo','crates','programs','tools/r1-cost-probe','scripts','xtask','audit/poseidon-pair-probe','docs/research/v8-r0-zk-20261009/z4','docs/research/v8-r0-zk-20261009/c3','docs/research/v8-r0-zk-20261009/refine']
def git(*args):return subprocess.check_output(['git',*args],cwd=ROOT,text=True).strip()
def data():
 paths=git('ls-files',*ROOTS).splitlines()
 pins={p:{'sha256':hashlib.sha256((ROOT/p).read_bytes()).hexdigest(),'bytes':(ROOT/p).stat().st_size} for p in sorted(paths) if (ROOT/p).is_file()}
 chain=[]
 for p,needle,role in ROUTES:
  lines=(ROOT/p).read_text().splitlines(); locations=[i for i,s in enumerate(lines,1) if needle in s]
  assert len(locations)==1,(p,needle,locations)
  chain.append(dict(file=p,line=locations[0],symbol_or_call=needle,role=role))
 subprocess.run(['git','diff','--exit-code','research','--','crates','programs'],cwd=ROOT,check=True,stdout=subprocess.DEVNULL)
 return dict(schema='aspis.pv-client-pins.v1',source_revision=git('rev-parse','HEAD'),implementation_base='149855299b',candidate_reuse='1dfbd5711684d73fc2ff664cfae9ae78f7dd34f8',scope='Conservative tracked source/build/dependency superset, not a minimal reachability theorem. Registry/Pool host codecs are unchanged. External Cargo dependencies are pinned through both Cargo.lock files; their vendored sources are not claimed.',roots=ROOTS,crates_programs_unchanged_from_research=True,headline_rust_entry='devnet_spend::main, action=prove branch, called by scripts/r1_devnet_spend.py through Client64_proof_accounts.proof_plan; selected inner entry devnet_spend::plan::prove',headline_binding_obligation='Instantiate FSExperiments.real and observe with the COMPLETE client execution, including Python lifecycle, signing/publication, files/ledger, errors, cleanup and L1/L2/L3/oracle/TLS events. This JSON does not supply RustRealRefinement, RunJoin, E1 or E2.',call_chain=chain,files=pins)
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--check',action='store_true');a=parser.parse_args();out=E/'client-pins.json'
 if a.check:
  old=json.loads(out.read_text());new=data()
  for k in ('files','call_chain','crates_programs_unchanged_from_research','headline_rust_entry','headline_binding_obligation'):assert old[k]==new[k],k
  print('PASS:',len(old['files']),'source pins and exact entry chain; no crates/programs delta')
 else:out.write_text(json.dumps(data(),indent=2,sort_keys=True)+'\n');print(out)
if __name__=='__main__':main()
