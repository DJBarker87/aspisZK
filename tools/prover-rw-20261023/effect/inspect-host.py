"""Read-only inventory of the exact caller-005 backend; no extraction launched."""
from pathlib import Path
import hashlib,json,subprocess,datetime
base=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain')
h=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023')
def pin(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
files=['src/Config.ml','src/Main.ml','src/llbc/FunsAnalysis.ml','src/symbolic/SymbolicToPureTypes.ml','src/pure/Pure.ml']
items=[]
for rel in files:
 p=base/'aeneas-full'/rel;s=p.read_text();lines=s.splitlines()
 terms=['stateful','state-error','state ->','compute_raw_fun_effect_info']
 ranges=set()
 for i,line in enumerate(lines):
  if any(t in line for t in terms):ranges.update(range(max(0,i-3),min(len(lines),i+9)))
 items.append(dict(**pin(p),state_related_lines=[dict(line=i+1,text=lines[i]) for i in sorted(ranges)]))
r=h/'src/receipts/aeneas-caller-005/receipt.json'
old=json.loads(r.read_text());exe=Path(old['target'][0])
extract_receipt=h/'src/receipts/extract-caller-005/receipt.json'
ex=json.loads(extract_receipt.read_text())
extract_script=h/'src/tools/prover-rw-20261023/extract-opening.py'
charon=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
receipt=dict(charon_binary=pin(charon),charon_cached_version=json.loads((h/'tool-versions.json').read_text())['charon'],charon_extraction_receipt=pin(extract_receipt),charon_extraction_entry=ex['target'],charon_driver=pin(extract_script),charon_driver_text=extract_script.read_text(),charon_driver_matches_retained_extraction=pin(extract_script)['sha256']==ex['source_sha256']['tools/prover-rw-20261023/extract-opening.py'],schema='prover-rw-effect-interface-inspection-v1',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),source_revision='7db89a0216818294add9efa77101568aed1a3629',mode='read-only source inspection; no Lean/Kani/extraction launches',caller005_receipt=pin(r),exact_command=old['target'],backend_binary=pin(exe),backend_source_revision=subprocess.check_output(['git','-C',str(base/'aeneas-full'),'rev-parse','HEAD'],text=True).strip(),backend_source_dirty=subprocess.check_output(['git','-C',str(base/'aeneas-full'),'status','--porcelain'],text=True),inspected_sources=items,llbc=pin(h/'src/ProverRwCaller.llbc'),assessment='No usable implicit world-state extraction interface: stateful analysis field is not part of translated fun_effect_info; no Config/Main state switch. Commented state-error examples are not an implementation. Existing pure extraction does not justify arbitrary stateful specialization.',new_trust_used=False)
print(json.dumps(receipt,indent=2))
