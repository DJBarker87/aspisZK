from pathlib import Path
import hashlib,json,re,subprocess
E=Path(__file__).resolve().parent.parent
M=json.loads((E/'final-manifest.json').read_text())
receipts=[json.loads(p.read_text()) for p in (E/'lean').glob('J*.json')]
records=[]
for root in M['roots']:
 p=Path(root['path']);sha=hashlib.sha256(p.read_bytes()).hexdigest()
 matches=[x['attempt'] for x in receipts if x.get('exit')==0 and x.get('source_sha256')==sha and x.get('module',x.get('target'))==root['module']]
 assert matches,(root['module'],'no accepted matching source')
 records.append(dict(module=root['module'],sha256=sha,accepted_receipts=matches))
a=json.loads((E/'lean/J10572.json').read_text())
ax=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",a['out'])
assert all(set(re.split(r',\s*',v)) <= {'propext','Classical.choice','Quot.sound'} for k,v in ax)
base='3bf0a58481bc98110878803c3d8aacfec2371375'
paths=[Path(x) for x in subprocess.check_output(['git','diff','--name-only',base,'HEAD'],text=True).splitlines() if '/lean/' in x and x.endswith('.lean') and Path(x).is_file()]
paths.append(Path('docs/research/v8-r0-zk-20261009/lean/R1Z/ProverCommitAudit53.lean'))
for p in paths:
 s=p.read_text();s=re.sub(r'/\-.*?\-/','',s,flags=re.S);s=re.sub(r'--[^\n]*','',s)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b',s),p
shipped=subprocess.check_output(['git','diff','--name-only',base,'HEAD','--','crates','programs'],text=True).splitlines();assert not shipped
before=E/'endpoint/before.lean.txt';after=E/'endpoint/after.lean.txt';assert before.read_bytes()==after.read_bytes()
(E/'final-integrity.json').write_text(json.dumps(dict(source_revision='7cbabb93ed',root_sources=records,final_audit_attempt='J10572',axiom_report_count=len(ax),accepted_axioms_only=True,live_changed_lean_files_scanned=len(paths),forbidden_proof_tokens=[],shipped_files_changed=shipped,endpoint_before_after_equal=True,endpoint_sha256=hashlib.sha256(before.read_bytes()).hexdigest(),next_compile_attempt='J10573'),indent=2)+'\n')
print('roots',len(records),'axiom reports',len(ax),'live Lean files',len(paths))
