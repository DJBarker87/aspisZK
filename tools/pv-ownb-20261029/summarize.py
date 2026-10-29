from pathlib import Path
import json,re,datetime,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownb-20261029'
rs=[json.loads(p.read_text())for p in sorted(E.glob('lean-*/receipt.json'))]
assert len(rs)==100 and {r['attempt']for r in rs}==set(range(62500,62600))
failed=[r['attempt']for r in rs if r['exit']!=0]
axioms=(E/'lean-62598/output.log').read_text();assert 'sorryAx'not in axioms
found=re.findall(r"depends on axioms: \[([^\]]*)\]",axioms)
assert all(set(x.strip()for x in a.split(',')if x.strip())<={'propext','Classical.choice','Quot.sound'}for a in found)
queries=len(re.findall(r"^'[^']+' (?:depends on|does not depend)",axioms,re.M));assert queries==118,queries
barriers=[]
for p in sorted(E.glob('*/receipt.json')):
 for filename in ['admission-before.json','admission-barrier.json']:
  a=json.loads((p.parent/filename).read_text());assert a['allowed'] is True,(p,filename)
 a=json.loads((p.parent/'admission-barrier.json').read_text());barriers.append(dict(scope=p.parent.name,utc=a['utc']))
early=json.loads((E/'early-launch-admissions.json').read_text());assert all(a['allowed']for a in early)
for p in E.glob('*/admission-launch.json'):assert json.loads(p.read_text())['allowed']is True
refused=datetime.datetime.fromisoformat('2026-10-29T00:24:22.722245+00:00')
retry=datetime.datetime.fromisoformat(json.loads((E/'lean-62530/admission-barrier.json').read_text())['utc']);assert(retry-refused).total_seconds()>=180
assert not any(refused<datetime.datetime.fromisoformat(b['utc'])<refused+datetime.timedelta(seconds=180)for b in barriers)
summary=dict(lean_starts=100,lean_passed=100-len(failed),lean_failed=failed,native_scopes=len(list(E.glob('native-*/receipt.json'))),kani=0,axioms_queries=queries,axioms_only=['propext','Classical.choice','Quot.sound'],max_lean_rss_kib=max(int(r['peak_rss_kib'])for r in rs),all_lean_swap_zero=all(str(r['swap'])=='0'for r in rs),audit_rows=[{k:r[k]for k in ['attempt','module','exit','wall','peak_rss_kib','swap','source_revision','source_sha256']}for r in rs if r['attempt']>=62597],admission_violation_found=False,refusal_retry_seconds=(retry-refused).total_seconds(),refusal_evidence_limit='raw refused barrier JSON overwritten by same-ID retry; time and decision retained in RESUME.md and conversation tool output; cooldown checked against accepted scope timestamps',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),rows={r:'SUSPENDED'for r in ['V229','V230','V239','V178']},endpoint_premises=dict(removed=0,added=0,changed=0))
(E/'combined-audit.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
