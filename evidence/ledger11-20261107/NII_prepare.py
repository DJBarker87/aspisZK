"""Own ledger11 adapters; predecessor validators and walker are unchanged."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent; P=E.parent/'ledger10-20261106'
JOBS={'NHK':'transcript-queries3-20261106/NHK_validate.py','NHN':'q-leftovers-20261106/NHN_validate.py','NHG':'verify-observed2-20261106/NHG_final_validate.py','NHS':'prepared-close-20261106/NHS_certify.py','NHM':'slice-d-pair2-20261106/NHM_validate.py','NHJ':'slice-d-entry3-20261106/NHJ_certify.py','NHX':'slice-d-pair3-20261106/NHX_validate.py','NHU':'verify-observed3-20261106/NHU_validate2.py','NHP':'pool-b3-20261106/NHP_validate.py'}
s=(P/'NHO_replay.py').read_text().replace('NHO','NII');i=s.index('jobs={');j=s.index('\ntry:\n path=',i);s=s[:i]+'jobs='+repr({a:'evidence/'+p for a,p in JOBS.items()})+s[j:];s=s.replace("(['--final'] if task in ['NGY','NHC'] else [])","[]")
# Nested evidence-only validator scripts run under the same read/write sandbox.
insert='''
raw_run=subprocess.run
nested=[]
def sandbox_run(args,*a,**kw):
 if isinstance(args,list) and len(args)>1 and str(args[0])==sys.executable and str(args[1]).endswith('.py'):
  p=Path(args[1]);assert p.is_relative_to(R),('external validator process',args)
  oldargv=sys.argv;sys.argv=list(map(str,args[1:]));buf=io.StringIO();rc=0
  import contextlib
  try:
   with contextlib.redirect_stdout(buf),contextlib.redirect_stderr(buf):
    exec(compile(get(p),str(p),'exec'),{'__file__':str(p),'__name__':'__main__'})
  except SystemExit as e:rc=e.code or 0
  finally:sys.argv=oldargv
  nested.append(dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(get(p)).hexdigest(),exit=rc))
  out=buf.getvalue();result=subprocess.CompletedProcess(args,rc,out if kw.get('text') else out.encode(),'' if kw.get('text') else b'')
  if kw.get('check') and rc:raise subprocess.CalledProcessError(rc,args,output=result.stdout)
  return result
 return raw_run(args,*a,**kw)
subprocess.run=sandbox_run
'''
s=s.replace('task=sys.argv[1];rc=0',insert+'\ntask=sys.argv[1];rc=0');s=s.replace('result=result,sparse_inputs=used','result=result,nested_validators=nested,sparse_inputs=used')
(E/'NII_replay.py').write_text(s)
# Runtime-only driver naming substitutions; proof/scanner algorithms unchanged.
for n in ['run.py','batch.py','ProofDriver.lean','Driver.lean']:
 s=(P/('NHO_'+n)).read_text().replace('NHO','NII').replace('codex-cx-ledger10-20261106','codex-cx-ledger11-20261107')
 (E/('NII_'+n)).write_text(s)
(E/'NII_VALIDATOR_JOBS.json').write_text(json.dumps(JOBS,indent=1)+'\n')
