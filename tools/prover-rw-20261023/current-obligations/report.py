#!/usr/bin/env python3
"""Evidence inventory for the selected source instance, not a proof score."""
from pathlib import Path
import hashlib,json,subprocess,sys
root=Path(__file__).resolve().parents[3];out=Path(sys.argv[1])
subprocess.run([sys.executable,str(root/'tools/prover-rw-20261023/query-obligations.py'),str(out)],check=True,stdout=subprocess.DEVNULL)
x=json.loads(out.read_text());installed=[12,112,113,115,116,233,234,248]
pins={}
for name in ['ProverRwOuterMapErr','ProverRwOuterGuardLeaves','ProverRwOuterTag','ProverRwOuterContext','ProverRwCallerBinding']:
 p=root/f'docs/research/v8-r0-zk-20261009/lean/R1Z/{name}.lean';pins[name]=hashlib.sha256(p.read_bytes()).hexdigest()
allids=set(x['dictionary']['remaining_entries'])|set(x['dictionary']['installed_preexisting'])
x['selected_source_dictionary']=dict(selected='ProverRwOuterMapErr.selected',installed=installed,remaining_entries=sorted(allids-set(installed)),remaining_count=len(allids-set(installed)),source_pins=pins,scope='Proved source operation interpretations only; native representation/effect association remains open for all required operations.')
x['caller_contracts']=dict(PrefixContract='No concrete instance; public serializer/native byte representation, ordered ROM/TLS and reservation path association remain.',BodyContract='No concrete instance; actual rejected reservation branch proved, successful mask/proof/audit/state equation remains.')
x['entropy']=dict(attempts=8,fills_per_attempt=16,bytes_per_fill=64,source_world='Arbitrary typed full/error finite sequence proved with complete ordered reads; at most sixteen consumed fills; no residual artificial retry boundary.',native='Native callback/extractor/ABI/drop and history-conditioned E1 carrier association OPEN.',conditional_model_bounds=dict(sixteen_zero_exhaustion='2^-4080',eight_hazards='2^-4077',qualification='Conditional E1 on exact history frame, normalized next-context kernels and substochastic outer retry; OS/errors/divergence remain explicit. Not installed native probabilities.'),excluded_calls='The128 cap concerns the private entropy callsite, not arbitrary external account-policy calls.')
x['native_effect_cut']=dict(local_operation_leaves=41,type_leaves=16,native_body_subset_local_leaves=35,scope='Cut inventory, not discharged native assumptions.')
x['unchanged_root_premises_removed']=0
x['next_deliverable']='A source/extractor-justified native effect association retaining callbacks, failures, ordered ROM/TLS, ledger and observer state; instantiate E1 at exactly its retained conditioning frame, then concrete outer PrefixContract and successful BodyContract and complete real RunJoin.'
out.write_text(json.dumps(x,indent=2)+'\n');print(json.dumps(dict(selected_remaining=x['selected_source_dictionary']['remaining_count'],root_premises_removed=0)))
