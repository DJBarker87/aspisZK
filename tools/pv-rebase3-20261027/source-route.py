"""Bind the selected native route to D162's pinned client chain without execution."""
import hashlib,json,pathlib,subprocess
root=pathlib.Path(__file__).resolve().parents[2]
out=root/'evidence/pv-rebase3-20261027'
paths=['scripts/r1_devnet_spend.py','scripts/Client64_proof_accounts.py','tools/r1-cost-probe/src/bin/devnet_spend.rs','tools/r1-cost-probe/src/bin/devnet_spend/plan.rs','tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs','crates/aspis-r1-cost-probe/src/RealR1_client.rs','crates/aspis-prover/src/state_only_entropy.rs']
rows=[]
for p in paths:
 b=(root/p).read_bytes();pinned=subprocess.check_output(['git','show','5228877938:'+p],cwd=root)
 rows.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),matches_pinned_client=b==pinned))
assert all(x['matches_pinned_client'] for x in rows[:-1])
assert (root/paths[-1]).read_bytes()==subprocess.check_output(['git','show','237e135561:'+paths[-1]],cwd=root)
rows[-1]['rule']='D187 candidate entropy rewrite retained; same selected64 API and 64-byte fill, not byte-identical research source'
chain=json.loads((root/'evidence/pv-client-20261026/client-pins.json').read_text())['call_chain']
for node in chain:
 text=(root/node['file']).read_text()
 assert node['symbol_or_call'] in text,node
 node['pinned_line']=node['line']
 node['line']=text[:text.index(node['symbol_or_call'])].count('\n')+1
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),pinned_client_revision='5228877938c7e42a1c87aa35f69f9a110ee9a4d6',files=rows,call_chain=chain,scope='Exact source equality for the client planner/account/adapter chain; selected64 entropy API uses the preserved D187 candidate implementation. Candidate prover rewrite is intentionally retained; this is not whole-source equality to research or a formal refinement proof.')
(out/'source-route.json').write_text(json.dumps(result,indent=2)+'\n')
print('Pinned planner/account/adapter match: six files; candidate entropy rewrite retained;',len(chain),'source chain entries')
