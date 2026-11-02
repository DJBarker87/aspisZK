from pathlib import Path
import subprocess,json,hashlib,time
E=Path(__file__).resolve().parent;sha=lambda b:hashlib.sha256(b).hexdigest()
def get(rev,p):return subprocess.check_output(['git','show',rev+':'+p])
refs={n:subprocess.check_output(['git','rev-parse',r],text=True).strip()for n,r in [('runjoin','codex/pv-runjoin-20261026'),('research','research'),('b3p6','codex/pv-b3p6-20261028')]};old=json.loads((E/'CURRENT-SCOPE-PINS.json').read_text());checks=[]
for x in old['sources']:
 b=get(refs['runjoin'],x['path']);checks.append({'path':x['path'],'old_revision':x['revision'],'current_revision':refs['runjoin'],'sha256':sha(b),'unchanged':sha(b)==x['sha256']});assert checks[-1]['unchanged'],x['path']
p='design/PRIVACY-LEDGER-20261026.md';a=get(old['refs']['research'],p);b=get(refs['research'],p);assert a==b
copies=[]
for group,p,name in [('b3p6','evidence/pv-b3p6-20261028/resume18/HANDOFF.md','B3-LATEST-HANDOFF.md'),('b3p6','evidence/pv-b3p6-20261028/resume18/PER-FUNCTION-D554.json','B3-PER-FUNCTION-D554.json'),('runjoin','evidence/pv-runjoin72-20261102/REPORT-D552.md','RUNJOIN-D552-REPORT.md'),('runjoin','evidence/pv-runjoin72-20261102/HANDOFF.md','RUNJOIN-D552-HANDOFF.md'),('runjoin','evidence/pv-runjoin73-20261102/REPORT-D564.md','RUNJOIN-D564-REPORT.md'),('runjoin','evidence/pv-runjoin73-20261102/HANDOFF.md','RUNJOIN-D564-HANDOFF.md')]:
 raw=get(refs[group],p);(E/'current-scope'/name).write_bytes(raw);copies.append({'revision':refs[group],'path':p,'sha256':sha(raw),'retained_copy':'current-scope/'+name})
f=json.loads((E/'current-scope/B3-PER-FUNCTION-D554.json').read_text());kani=[x for x in f['functions']if 'kani'in x['route'].lower()];assert len(kani)==2
out={'epoch':time.time(),'refs':refs,'prior_refs':old['refs'],'installed_source_checks':checks,'research_ledger_unchanged':True,'ledger_sha256':sha(b),'current_b3_counts':f['counts'],'current_b3_kani_bodies':kani,'copies':copies,'disposition':'All 36 local V244 associations are now bound; same two Kani properties as prior pin. Full callback/std/D188/native closure remains OPEN. Installed selector source files and all ledger cells are unchanged.'};(E/'CURRENT-SCOPE-REFRESH-D549.json').write_text(json.dumps(out,indent=2)+'\n');print({'refs':refs,'counts':f['counts'],'Kani':[(x['function'],x['evidence'])for x in kani]})
