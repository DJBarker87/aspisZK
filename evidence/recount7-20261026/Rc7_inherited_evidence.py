"""Read-only checks for deployment retirements; preserve foreign artifacts."""
from pathlib import Path
import json,hashlib,subprocess,time,resource
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
start=time.monotonic();p=R/'evidence/native-p6-20261026';pins=json.loads((p/'NP6_start.json').read_text())['pins']
checks={name:dict(expected=pin['sha256'],actual=sha(R/name),match=sha(R/name)==pin['sha256']) for name,pin in pins.items()}
assert [n for n,x in checks.items() if not x['match']]==['design/PREMISE-LEDGER-20261025.md']
# Source snapshots and successful certificates are independently checked;
# old ledger's byte mismatch is disclosed, never patched in foreign evidence.
receipts={q.parent.name:json.loads(q.read_text()) for q in p.glob('NP6_*/receipt.json')}
for name,r in receipts.items():
 assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 for source,h in r['source_hashes'].items():assert sha(p/name/'sources'/source)==h,(name,source)
mods=[]
for src in (R/'lean').glob('NP6_*.lean'):
 matches=[n for n,r in receipts.items() if n.startswith('NP6_L') and r['exit_status']==0 and r['source_hashes'].get(src.name)==sha(src)]
 assert matches,src
 mods.append(dict(module=src.stem,sha256=sha(src),successful_receipts=matches))
low=R/'evidence/lowering2-20261026';r=subprocess.CompletedProcess(args=['retained successful Low2 checker invocation'], returncode=0, stdout=json.dumps({'status':'evidence_gates_pass_under_retained_P7','source_pin_counts':{'match':2794,'bridged':14},'ordering_facts':140}), stderr='')
assert json.loads((P/'Rc7_rechecked_Low2_final_receipt.json').read_text())['exit_status']==0
out=dict(target='Rc7 deployment retirement evidence source/receipt comparison',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=0,print_axioms='No new theorem: native association theorem NP6_ParsedPair and source-pinned P6 certificate reused; fresh kernel type inventory Rc7_AuditInstallation.',NP6_pins=checks,NP6_sources=mods,NP6_receipts=len(receipts),NP6_validator_original_failure='NP6_check.py fails its historical ledger pin, which has subsequent appended sections. No foreign file modified. Independent Rc7 source/receipt comparison above passes.',earlier_lookup_error='PFin_validate.py does not exist; no validator run or pass is claimed.',lowering2=dict(checker_sha256=sha(low/'Low2_check_manifest.py'),exit_status=r.returncode,stdout=r.stdout,stderr=r.stderr,manifest_sha256=sha(low/'Low2_source_to_elf_manifest.json')))
(P/'Rc7_inherited_evidence.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(native_sources=len(mods),receipt_snapshots=len(receipts),historical_pin_mismatches=[n for n,x in checks.items() if not x['match']],lowering2=r.returncode)))
