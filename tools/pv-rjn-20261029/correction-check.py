"""Check that the private node correction preserves every original conjunct."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];D=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';E=R/'evidence/pv-rjn-20261029'
p='docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_PublishSkeleton54.lean'
before=subprocess.check_output(['git','show','c8fb38ee73:'+p],text=True).split('def PV_RunJoin_Link_NodeAppend',1)[1].split('/-- Local serializer',1)[0].strip()
source=(D/'PV_RJN_NodeContext.lean').read_text();after=source.split('def PV_RJN_Link_NodeAppend',1)[1].split('def PV_RJN_Link_PublishOrder',1)[0].strip()
insertion=' QueryRange p.queries → QueryContext (runs i) p →'
assert after.replace(insertion,'')==before
out=dict(before_path=p,after_path=str((D/'PV_RJN_NodeContext.lean').relative_to(R)),before='def PV_RunJoin_Link_NodeAppend'+before,after='def PV_RJN_Link_NodeAppend'+after,only_change='Insert explicit QueryRange and QueryContext preconditions; rename in private prefix',all_original_conjuncts_verbatim=True,existing_definitions_edited=False,separate_obligations=['PublishSkeleton57.PV_RunJoin_Link_QueryRange','PublishContext57.PV_RunJoin_Link_QueryContext'],candidate_status='UNVERIFIED as a decomposition; corrected NodeAppend itself and simultaneous-link witness remain open')
producers=[]
for path in D.glob('PV_RJN_*.lean'):
 for m in re.finditer(r'^def (PV_RJN_Producer_\w+).*?(?=^theorem |^def |^#print|\Z)',path.read_text(),re.S|re.M):
  body=m[0];assert not any(x in body for x in ['PV_RunJoin_Link_','PV_RJN_Link_','ProverCommitPublish43.assemble','prover.append_node_slots','prover.append_query_openings','resultBytes'])
  producers.append(dict(module=path.stem,name=m[1],sha256=hashlib.sha256(body.encode()).hexdigest(),statement=body.strip()))
out['standalone_producer_statements']=producers
(E/'node-link-before-after.json').write_text(json.dumps(out,indent=2)+'\n');print('Original node conjuncts preserved; standalone producers:',len(producers))
