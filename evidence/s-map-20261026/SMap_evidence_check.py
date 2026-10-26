"""Read foreign release packets; write only this audit's receipt. No compilers."""
from pathlib import Path
import hashlib,json,resource,subprocess,time
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
start=time.monotonic();low=R/'evidence/lowering2-20261026'
inputs=load(low/'Low2_build_inputs.json');pins=load(low/'Low2_source_pin_check.json')
build=load(low/'Low2_build_manifest.json');manifest=load(low/'Low2_source_to_elf_manifest.json')
for p,h in inputs['files'].items():assert sha(R/p)==h,p
for x in pins['evidence_files']:assert sha(R/x['path'])==x['sha256'],x
assert not pins['errors']
for x in pins['verification_source_pins']:
 assert x['retained_exact_files']
 for p in x['retained_exact_files']:assert sha(R/p)==x['expected_sha256'],p
elf={'default':'f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4','devnet':'63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299','pool':'121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548'}
for x in build['builds']:
 assert x['receipt']['exit_status']==0 and x['receipt']['swaps']==0
 assert x['artifact']['sha256']==x['artifact']['expected_sha256']==elf[x['mode']]
 assert x['artifact']['byte_identical']
assert manifest['status']=='evidence_gates_pass_under_retained_P7'
assert manifest['s10']['facts']==140 and manifest['s10']['all_preserved']
inherited=load(R/'evidence/recount7-20261026/Rc7_inherited_evidence.json')
for x in inherited['NP6_sources']:assert sha(R/'lean'/(x['module']+'.lean'))==x['sha256'],x
for p,x in inherited['NP6_pins'].items():
 if p!='design/PREMISE-LEDGER-20261025.md':assert sha(R/p)==x['expected'],p
usage=resource.getrusage(resource.RUSAGE_SELF)
out=dict(target='SMap L186 artifact and NP6 source evidence audit',command=['python3','-B','evidence/s-map-20261026/SMap_evidence_check.py'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss,swaps=usage.ru_nswap,print_axioms='Not a Lean theorem; NP6 composition checked separately in SMap_015; retained P7 is not a Lean axiom',compiler_inputs_compared=len(inputs['files']),packet_evidence_files_compared=len(pins['evidence_files']),verification_source_pins=len(pins['verification_source_pins']),NP6_sources_compared=len(inherited['NP6_sources']),historical_ledger_mismatch='Retained; old NP6 ledger hash predates appended recount sections',artifacts=elf,ordering_facts=140,rebuilt_in_this_audit=False,foreign_checker_not_run='Low2_check_manifest.py writes foreign manifest/receipt; independent read-only comparisons used instead',input_hashes={str(p.relative_to(R)):sha(p) for p in [low/'Low2_source_to_elf_manifest.json',low/'Low2_final_receipt.json',R/'evidence/recount7-20261026/Rc7_premises.json']})
(E/'SMap_artifact_audit.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['exit_status','compiler_inputs_compared','NP6_sources_compared','ordering_facts']}))
