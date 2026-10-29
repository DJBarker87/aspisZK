"""Validate evidence and summarize exact targets/resources/source/axiom results."""
from pathlib import Path
import subprocess,json,hashlib,lzma,re
E=Path('evidence/pv-rdb2f-20261029');P=Path('docs/research/v8-r0-zk-20261009/lean/R1Z');allowed={'propext','Classical.choice','Quot.sound'};rows=[]
for n in range(63300,63400):
 p=E/f'lean-{n}/receipt.json';j=json.loads(p.read_text());assert j['attempt']==n and j['swap']=='0'
 assert hashlib.sha256(subprocess.check_output(['git','show',j['source_blob']])).hexdigest()==j['source_sha256']
 for f in ['admission-before.json','admission-launch.json','admission-barrier.json']:assert json.loads((p.parent/f).read_text())['allowed']is True
 if j['exit']==0:
  for ax in j['print_axioms']:
   m=re.search(r'depends on axioms: \[([^]]*)\]',ax,re.S)
   if m:assert {s.strip()for s in m[1].split(',')}<=allowed,(n,ax)
 j['dependency_fingerprint']='closure-fingerprint.json.xz'if j['exit']==0 else None
 j['credit']='coherent source/model proof, scope stated in per-row binding'if j['exit']==0 else 'failed elaboration/staging; no proof credit; any sorryAx output rejected'
 if n==63397:j['print_axioms_reference']='63398 performs the 137-declaration axiom audit; this target prints statements only'
 p.write_text(json.dumps(j,indent=2)+'\n');rows.append(j)
raw=lzma.decompress((E/'closure-fingerprint.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/'closure-fingerprint.json.sha256').read_text().strip();fp=json.loads(raw)
manifest=json.loads((E/'frozen-proof-manifest.json').read_text());lookup={r['module']:r for r in fp['objects']}
for r in manifest['modules']:
 p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['source_sha256']==lookup[r['module']]['source']['sha256']
for p in P.glob('PV_RDB2F_*.lean'):
 s=re.sub(r'/\-.*?\-/','',p.read_text(),flags=re.S);s=re.sub(r'--[^\n]*','',s)
 assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',s),p
 assert not re.search(r'^import .*\bXR',s,re.M),p
assert not subprocess.check_output(['git','diff','--name-only','50c43a49d6','--','crates','programs','design'],text=True).strip()
scopes=[]
for p in sorted(E.glob('*/receipt.json')):
 if p.parent.name.startswith('lean-'):continue
 j=json.loads(p.read_text());assert j['swap']=='0'
 for f in ['admission-before.json','admission-launch.json','admission-barrier.json']:assert json.loads((p.parent/f).read_text())['allowed']is True
 scopes.append(dict(name=p.parent.name,receipt=str(p.relative_to(E)),**j))
assert len(scopes)==10
assert len(rows)==100 and len(manifest['theorems'])==80 and len(manifest['named_declarations'])==137
assert all(j['exit']==0 for j in rows[-3:])
for p in E.rglob('*'):
 if p.is_file():assert p.stat().st_size<=20_000_000,p
j=dict(branch='codex/pv-rdb2f-20261029',base='50c43a49d6',worktree=str(Path.cwd()),restored=[],suspended=['V256','V257','V231'],V231='software path proved; SHA-NI path conditional on R1Z.PV_RDB2F_ShaNi.SHA_NI_IntrinsicsSemantics, pending owner item3',evidence_class='class B; structural (K-1 substitute) under own-1; V370/D381/D386 retained',lean=dict(used=100,limit=100,exit_zero=sum(r['exit']==0 for r in rows),exit_nonzero=sum(r['exit']!=0 for r in rows),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rows),swap=0),native=dict(used=len(scopes),limit=40,kani=0,peak_rss_kib=max(int(r['peak_rss_kib'])for r in scopes),swap=0),attempts=rows,scopes=scopes,statement_audit=63397,axioms_audit=63398,focused_replay=63399,new_theorems=80,audited_declarations=137,project_objects=len(fp['objects']),external_objects=len(fp['external']),registry_sources=len(fp['registry_sources']),R72_cohort_authority='r72-cohort.json',axioms=sorted(allowed),endpoint_theorem_text_changed=False,endpoint_premises_textually_removed=0,local_source_P_discharged=[],local_source_laws_proved=['V256 original mutable source/caller law in recorded cohort','V257 original mutable source/caller law in recorded cohort'],same_literal_LEAN_PATH=False,restoration_gate='Requested exact original LEAN_PATH not preserved; leading private prefix renamed; credit withheld; ENVIRONMENT_FINDING.md',T=['entropy_law','entropy_kernel','observation'],T_changed=False,composition_trust='reclassification within existing tool trust, never premise removal',process_deviations='process-deviations.json',stop='100 Lean attempts used; V256/V257 restoration withheld pending exact-LEAN_PATH R72 replay; V231 remains pending owner item3',next='Renewed budget: fresh R72 and all affected unchanged consumers under exact original LEAN_PATH; then assess sampler restoration. Owner decides SHA-NI item3.')
(E/'combined-audit.json').write_text(json.dumps(j,indent=2)+'\n')
for row in ['V256','V257','V231']:
 (E/(row+'.json')).write_text(json.dumps(dict(row=row,disposition='SUSPENDED',class_='B',evidence_class=j['evidence_class'],detail=row+'.md',hypothesis='R1Z.PV_RDB2F_ShaNi.SHA_NI_IntrinsicsSemantics'if row=='V231'else None,compiler_obligation_retained='V370; D381/D386',statement_audit=63397,axioms_audit=63398,replay=63399,T_changed=False),indent=2)+'\n')
print(json.dumps({k:j[k]for k in ['lean','native','new_theorems','audited_declarations','project_objects','external_objects']}))
