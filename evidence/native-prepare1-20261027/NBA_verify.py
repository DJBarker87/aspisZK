"""Static receipt/source audit only. Launches no prover or build."""
from pathlib import Path
import json,hashlib,re,subprocess
E=Path(__file__).resolve().parent
errors=[];ledger=[];qualifications=[]
transport=[json.loads(s) for s in (E/'NBA_STEP_TRANSPORT.jsonl').read_text().splitlines()]
allowed={'propext','Classical.choice','Quot.sound'}
for p in sorted(E.glob('NBA_[KL]*/receipt.json')):
 r=json.loads(p.read_text());a=r['attempt'];kind=r['kind'];ledger.append(r)
 for key in ['module','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','limits','print_axioms']:
  if key not in r:errors.append([a,'missing',key])
 ad=json.loads((E/(a+'-reservation.json')).read_text())
 if ad.get('allowed') is not True:errors.append([a,'admission false'])
 admitted=False
 for t in transport:
  if t['attempt']!=a or t['submitted'] or t['exit']!=0:continue
  for line in t['stdout'].splitlines():
   try: x=json.loads(line)
   except json.JSONDecodeError:continue
   if isinstance(x,dict) and x.get('allowed') is True:admitted=True
 if not admitted:errors.append([a,'no exit0 AND allowed true admission'])
 if r['limits']!={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}:errors.append([a,'limits'])
 if str(r['swaps'])!='0':errors.append([a,'swap'])
 # Main submitted source is retained in every attempt's sources receipt.
 rel=r['sources'][0];s=p.parent/'sources'/rel
 if not s.exists() or hashlib.sha256(s.read_bytes()).hexdigest()!=r['source_hashes'][rel]:errors.append([a,'source snapshot'])
 if kind=='lean':
  if '-M7000' not in r['command'] or '-j1' not in r['command']:errors.append([a,'lean limits'])
  if r['exit_status']==0:
   for line in r['print_axioms']:
    if 'depends on axioms: [' in line:
     axs=set(line.split('depends on axioms: [',1)[1].split(']',1)[0].split(', '))-{''}
     if not axs<=allowed:errors.append([a,'nonstandard accepted axioms',line])
 else:
  g=json.loads((E/(a+'-graph-check.json')).read_text())
  if not g.get('graph_matches_frozen'):errors.append([a,'graph'])
  frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  after=(E/(a+'-lock-after.log')).read_text().split()[0]
  if g['lock_sha256']!=frozen or after!=frozen:errors.append([a,'lock drift'])
  if '--locked' in r['command'] or r['env'].get('CARGO_NET_OFFLINE')!='true' or r['env'].get('CARGO_PROFILE_DEV_OPT_LEVEL')!='3':errors.append([a,'kani invocation'])
  check=E/(a+'-source-check.json')
  if check.exists():
   x=json.loads(check.read_text())
   if x.get('errors'):errors.append([a,'scratch source drift'])
  elif a in ['NBA_K002','NBA_K003','NBA_K004','NBA_K005','NBA_K006','NBA_K007','NBA_K008','NBA_K009']:
   qualifications.append([a,('Rejected compile, submitted file hashes retained; no fresh full-source scan receipt. Graph and lock checks were fresh.' if a=='NBA_K002' else 'Earlier runner retained setup/per-run source manifest and submitted file hashes; no fresh full-source scan receipt. Graph and lock checks were fresh. Not retroactively described as a fresh source scan.')])
  else:errors.append([a,'missing source check'])
  pinfile=E/(a+'-source-pin.json')
  if pinfile.exists():
   pin=json.loads(pinfile.read_text())['source_sha256']
   for rel,h in r['source_hashes'].items():
    key=rel.removeprefix('NBA_src/')
    if key in pin and pin[key]!=h:errors.append([a,'receipt pin mismatch',key])
  elif a=='NBA_K002' and r['exit_status']!=0:
   qualifications.append([a,'Compile-only failure; source snapshot and four submitted file hashes retained, no full patch/source manifest retained for this rejected attempt.'])
  else:errors.append([a,'missing source pin'])
  log=(p.parent/'stdout.log').read_text()
  if r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' not in log:errors.append([a,'no successful Kani result'])
plan=json.loads((E/'NBA_AUDIT_PLAN.json').read_text());audit=json.loads((E/'NBA_L069/receipt.json').read_text())
for p,h in plan['source_sha256'].items():
 if hashlib.sha256(Path(p).read_bytes()).hexdigest()!=h:errors.append(['audit source changed',p])
roots=set(plan['roots']);printed={l.split("'",2)[1] for l in audit['print_axioms']}
if roots!=printed or audit['exit_status']!=0:errors.append(['axioms coverage',sorted(roots-printed),sorted(printed-roots)])
if hashlib.sha256(Path('lean/NBA_Audit.lean').read_bytes()).hexdigest()!=audit['source_hashes']['NBA_generated/NBA_Audit.lean']:errors.append(['audit main source'])
base=json.loads((E/'NBA_SCOPE.json').read_text())['base'];changed=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
if any(not(p.startswith('lean/NBA_') or p.startswith('evidence/native-prepare1-20261027/')) for p in changed):errors.append(['out-of-scope tracked edit'])
counts={k:dict(attempts=sum(r['kind']==k for r in ledger),passed=sum(r['kind']==k and r['exit_status']==0 for r in ledger)) for k in ['lean','kani']}
if counts['lean']['attempts']>100 or counts['kani']['attempts']>30:errors.append(['budget'])
summary=dict(status='OPEN',counts=counts,qualifications=qualifications,axioms_roots=len(roots),errors=errors,peak_rss_kib=max(int(r['peak_rss_kib']) for r in ledger),total_wall_seconds=sum(r['wall_seconds'] for r in ledger),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),preflight_only=['NBA_K001','NBA_K010','NBA_K011','NBA_L039'],qualification='Proof success does not close the native composite; see NBA_prepare_BRIDGE.md')
(E/'NBA_VERIFICATION.json').write_text(json.dumps(summary,indent=2)+'\n')
(E/'NBA_LEDGER.json').write_text(json.dumps(ledger,indent=2)+'\n')
print(json.dumps(summary));assert not errors
