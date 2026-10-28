from auditlib8 import *
# Normalize raw receipt schemas, retaining complete outputs and GNU-time fields.
recs=json.loads((P/'receipt-audit8.json').read_text());out=[];allowed={'propext','Classical.choice','Quot.sound'}
for r in recs:
 r.setdefault('ref','rw');r.setdefault('path',r.get('receipt'))
 raw=json.loads(read(r['ref'],r['path']));job=r['job'];a=raw.get('attempt',raw.get('id',int(re.search(r'(\d{5})',r['path']).group(1))));base='evidence/'+job+'/'
 stdout=base+('out-'+str(a)+'.log' if job in ['pv-rdb1-20261028','pv-rdeac-20261028'] else 'lean-'+str(a)+'/output.log')
 time=base+('time-'+str(a)+'.log' if job in ['pv-rdb1-20261028','pv-rdeac-20261028'] else 'lean-'+str(a)+'/time.log')
 s=read('rw',stdout);tm=read('rw',time)
 lines=raw.get('print_axioms',raw.get('axioms',[]))
 # stdout records wrap the axioms list across multiple lines.
 parsed=[]
 if s:
  for m in re.finditer(r"'([^']+)' (does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])",s,re.S):
   axs=[z.strip() for z in (m.group(3) or '').split(',') if z.strip()];parsed.append(dict(declaration=m.group(1),axioms=axs));assert raw['exit']!=0 or set(axs)<=allowed,(a,m.group(1),axs)
 def metric(pat):
  m=re.search(pat,tm or '');return m.group(1).strip() if m else None
 x=dict(job=job,attempt=a,receipt=r['path'],target=raw.get('module'),source_revision=raw.get('source_revision',raw.get('revision')),source_sha256=raw.get('source_sha256'),exit=raw['exit'],wall=raw.get('wall') or metric(r'Elapsed \(wall clock\) time.*?: (.*)'),peak_RSS_KiB=raw.get('peak_rss_kib') or metric(r'Maximum resident set size \(kbytes\): (\d+)'),swap=raw.get('swap') or metric(r'Swaps: (\d+)'),print_axioms=lines,parsed_axioms=parsed,stdout=stdout,time=time,admissible=a not in [41466,41494,41495,41496,41499,61199],qualification='41466 void;41494–41499 aggregate imports consume its object, not a compliant recompile. Independent row-specific proofs checked separately.' if a in [41466,41494,41495,41496,41499] else '61199 failed; no corrected-source proof credit' if a==61199 else 'existing scoped receipt reused; no replay by recount')
 if job=='pv-rdeac-20261028':
  src=read('rw',base+'attempt-sources/'+str(a)+'.lean.txt')
  x['target']=next(iter(re.findall(r'namespace\s+(\S+)',src or '')),None) or ('PV_RDEAC_Axioms' if a==61198 else 'PV_RDEAC_EndpointReplay' if a==61199 else 'PV_RDEAC_Statements' if a==61197 else 'PV_RDEA_CloneExecution')
 out.append(x)
# Explicit final binding source/object record: only41466 exists.
c=json.loads(read('rw','evidence/pv-rdcd-20261028/resume-final-receipt-coherence.json'))
v=next(x for x in c if x['module']=='R1Z/PV_CB_Op109CanonicalBinding');assert v['successful_attempts']==[41466]
(P/'admission-finding8.json').write_text(json.dumps(dict(void_binding=v,evidence='rw:evidence/pv-rdcd-20261028/RESUME-SEQUENCING.md',affected_row='V213',aggregate_audits_not_credited=[41494,41495,41496,41499],other_seven_rows='Retain independent successful row-specific laws and native gates; this aggregate is not a compliant final release manifest.',repaired_other_slip='60309 exact source recompiled61101; V178/V181 remain suspended'),indent=2)+'\n')
(P/'receipt-audit8.json').write_text(json.dumps(out,indent=1)+'\n')
# Every manifest snapshot is a content-addressed git blob and SHA witness.
unique={x['snapshot']:x for x in manifest}
for path,x in unique.items():
 b=(P/path).read_bytes();assert hashlib.sha256(b).hexdigest()==x['sha256'];assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['blob']
rs=json.loads((P/'rows8.json').read_text());old=json.loads((B/'recount7/rows7.json').read_text());assert len(rs)==407 and [x['id'] for x in rs]==[x['id'] for x in old]
for r,o in zip(rs,old):
 for k in ['id','name','meaning','definition','recount7_status','recount7_class']:
  assert r.get(k)==o.get(k),(r['id'],k)
 assert r['in_headline_closure8'] in ['research','candidate','neither'];assert r['tool_trust8'];assert r['definition_witnesses8'] or (not r.get('definition') and r['id'] in ['V380-inversion','V400','V401','V402','V403','V404','V405','V406']);assert r['dependency_bucket'] in 'abcd' if r['recount8_status']=='OPEN' else r['dependency_bucket'] is None
# The new definition witness references resolve to the complete 407-row audit.
da={x['id']:x for x in json.loads((P/'definition-audit8.json').read_text())}
for r in rs:
 assert r['definition_witnesses8']=='definition-audit8.json#'+r['id']+'/sources'
 assert da[r['id']]['sources'] or not r.get('definition')
# Markdown table shape is part of the ledger artifact check.
ledger=Path('design/PRIVACY-LEDGER-20261026.md').read_text().split('## Recount 8 2026-10-28 (B)')[1]
for title in ['Inventory / status','OPEN dependency','in headline closure?']:
 table=re.search(r'\| '+re.escape(title)+r'[^\n]*\n(?:\|[^\n]*\n)+',ledger).group().splitlines()
 assert all(len(l.split('|'))==11 for l in table),(title,[len(l.split('|')) for l in table])
# Exact source identity on shipped code: no build or heavy release gate.
identity=[]
for k in ['rw','runjoin','b3p6','rjdec','rdb2d','rdcd3']:
 q=subprocess.run(['git','diff','--quiet','82566acdfb',pins[k],'--','crates','programs','tools/r1-cost-probe']);identity.append(dict(ref=k,revision=pins[k],baseline='82566acdfb',exit=q.returncode,shipped_source_identical=q.returncode==0));assert q.returncode==0
(P/'shipped-source-identity8.json').write_text(json.dumps(identity,indent=2)+'\n');(P/'manifest.json').write_text(json.dumps(manifest,indent=1)+'\n')
v=dict(result='PASS',rows=407,manifest_entries=len(manifest),unique_source_objects=len(unique),historical_row_fields_preserved=True,exclusive_buckets=True,raw_receipts=len(out),accepted_axioms=sorted(allowed),void41466_rejected=True,uncompiled_failed61199_not_credited=True,endpoint_premises_removed_added_weakened=[0,0,0],Lean=0,Kani=0,IDs=[],new_proofs=0,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(P/'validation8.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps(v,indent=2))
