#!/usr/bin/env python3
"""Read-only proposal validation. This is not formal acceptance or a replay."""
from pathlib import Path
import gzip,hashlib,importlib.util,json,re
ROOT=Path(__file__).resolve().parents[5];BASE=ROOT/'docs/research/100bit-spend-path-20261013';E=BASE/'evidence/c2-recorded-current-audit-20261018'
sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
 p=json.loads((E/'proposal.json').read_text());z=(E/'candidate-closure.json.gz').read_bytes();raw=gzip.decompress(z);g=json.loads(raw)
 assert sha(z)==p['candidate_closure_gzip_sha256'] and sha(raw)==p['candidate_closure_sha256']
 assert g['classification']=='READ_ONLY_AUDIT_NO_LEAN_NO_OBJECT_REUSE'
 assert len(g['fresh_topological'])==g['fresh_target_count']==p['candidate_fresh_targets']==295
 assert len(g['current_base_boundaries'])==p['candidate_current_base_boundaries']==109
 assert p['unsupported_imports']==['AspisV8R19.R572SequentialWordMass']
 positions={m:i for i,m in enumerate(g['fresh_topological'])}
 for m,n in g['fresh_sources'].items():
  assert sha(n['source'].encode())==n['source_sha256'],m
  for dep in n['imports']:
   if dep in positions:assert positions[dep]<positions[m],(m,dep)
   else:assert dep in g['current_base_boundaries'] or dep in p['unsupported_imports'],dep
 spec=importlib.util.spec_from_file_location('inventory',BASE/'tools/j1-integrated-declaration-repin.py');inv=importlib.util.module_from_spec(spec);spec.loader.exec_module(inv)
 parser_spec=importlib.util.spec_from_file_location('model_parser',Path(__file__).with_name('model-command-parser.py'));parser=importlib.util.module_from_spec(parser_spec);parser_spec.loader.exec_module(parser)
 old=gzip.decompress((E/'superseded-proposal.json.gz').read_bytes());correction=p['hash_audit_correction']
 assert sha(old)==correction['original_proposal_sha256']
 assert sha((E/'superseded-proposal.json.gz').read_bytes())==correction['superseded_proposal_gzip_sha256']
 assert correction['graph_count_conclusions_changed']==False
 assert len(correction['corrections'])==49 and sum(n['changed'] for n in correction['corrections'])==8
 count=0
 for core in p['selected_definition_core_candidates']:
  n=g['fresh_sources'][core['source_module']];assert n['source_sha256']==core['source_sha256']
  declarations=parser.commands(n['source'],inv.lean_tokens,inv.canonical)
  assert core['proposal_only'] and not core['new_Lean_file_generated']
  for d in core['selected_definitions']:
   actual=declarations[d['qualified_declaration'].split('.')[-1]]
   assert actual['qualified_name']==d['qualified_declaration']
   assert actual==d['exact_command']
   assert actual['kind'] in ['def','abbrev','structure','inductive']
   count+=1
 assert count==p['selected_definition_count']==49
 s=g['fresh_sources']['C2RecordedExperimentConstruction']['source'];assert sha(s.encode())==p['final_source_sha256']
 assert s==(BASE/'lean/C2RecordedExperimentConstruction.lean').read_text()
 ts=[]
 for match in re.finditer(r'^theorem (\w+)\b',s,re.M):
  tail=s[match.start():];end=re.search(r'\n(?:theorem |#print axioms |end\b)',tail);b=tail[:end.start() if end else len(tail)];sig=b.split(':=',1)[0]
  ts.append({'name':'AspisR1.C2RecordedExperimentConstruction.'+match[1],'signature':sig,'signature_token_sha256':sha(inv.canonical(inv.lean_tokens(sig))),'body_token_sha256':sha(inv.canonical(inv.lean_tokens(b)))})
 assert ts==p['final_theorems'] and len(ts)==4
 print(json.dumps({'status':'PASS_READ_ONLY_AUDIT','candidate_targets_NOT_authorized':295,'unsupported_imports':p['unsupported_imports'],'core_candidates_NOT_generated':12,'selected_corrected_command_and_context_hashes':49,'superseded_body_hash_labels':49,'changed_command_hashes':8,'new_Lean_jobs':0,'new_formal_results':0,'actual_Backend_witness':'OPEN','small_current_model_closure':'NOT_YET_DEMONSTRATED'},sort_keys=True))
if __name__=='__main__':main()
