"""New candidate static/policy validation only. Never executes Lean or builds."""
import hashlib,json,os,pathlib,platform,resource,subprocess,sys,time
D=pathlib.Path('tools/port30join-20261025');E=pathlib.Path('evidence/port30join-20261025')
checks=[]
s=(D/'Port30JOIN_Composed.lean').read_text()
assert 'vops' not in s and 'data1' not in s
assert s.count('#print axioms accepted_original_sdk_s2_s1')==1
assert 'S2W_D189Consolidation.accepted_run L sdk' in s
assert 'S2W_InputSchedule.input_schedule installed H' in s
assert 'f = {rawCut with semantic := selectedPublic}' in s
assert 'rw [AspisS6SdkFirstObjectEquivalence.first_eq_original]' in s
n=(E/'sources/d346dc7cb7-S1SdkSelectedSemanticTraceV1.lean.txt').read_text()
span=n[n.index('      f.pub ='):n.index(' := by')].strip()
assert span in s, 'complete S1 postcondition text must remain'
for p in D.glob('*.lean'):
 t=p.read_text()
 for line in t.splitlines():
  if line.startswith('import '): assert all(m=='Lean' or m.startswith('Port30JOIN_') for m in line[7:].split())
 for forbidden in ['#eval!', 'native_decide','implemented_by','set_option maxHeartbeats','set_option maxRecDepth']:
  assert forbidden not in t,(p,forbidden)
checks.append('candidate textual association, full S1 postcondition and import/shortcut guards')
k=(D/'Port30JOIN_Kernel.lean').read_text()
assert 'do\n  throw (IO.userError "Port30JOIN kernel insertion disabled")' in k
assert 'private def replayDisabled' in k
assert 'Port30JOIN kernel calls disabled pending lead review/allocation' in k
assert '#eval' not in k and 'run_elab' not in k
checks.append('kernel insertion and replay unconditionally disabled; no invocation entry')
rows=[]
for label,argv,expected in [
 ('policy-tests',[sys.executable,'-B',str(D/'Port30JOIN_test_preflight.py')],0),
 ('expected-selection-rejection',[sys.executable,'-B',str(D/'Port30JOIN_preflight.py'),str(E/'selection-template.json')],1)]:
 start=time.monotonic()
 with (E/(label+'.stdout')).open('w') as out,(E/(label+'.stderr')).open('w') as err:
  proc=subprocess.Popen(argv,stdout=out,stderr=err)
  _,status,r=os.wait4(proc.pid,0);proc.returncode=os.waitstatus_to_exitcode(status)
 elapsed=time.monotonic()-start
 row=dict(target=label,argv=argv,exit=proc.returncode,expected_exit=expected,wall_seconds=elapsed,
          peak_rss_bytes=r.ru_maxrss if sys.platform=='darwin' else r.ru_maxrss*1024,swap=r.ru_nswap,
          axioms='N/A: Python policy/text checks, no theorem/kernel validation')
 rows.append(row);assert proc.returncode==expected,row
pins=[]
for folder in [D,E/'sources']:
 for p in sorted(folder.iterdir()):
  if p.is_file():
   b=p.read_bytes();pins.append(dict(path=str(p),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
report=dict(status='text/policy checks PASS; no kernel or theorem result',static_checks=checks,results=rows,
 source_revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),
 source_state='additional candidate edits pinned by file hashes; commit follows receipt',pins=pins,
 compiler_budget_spent=0,host_budget_spent=0,network_budget_spent=0,keys_accessed=False)
(E/'validation.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status=report['status'],results=rows)))
