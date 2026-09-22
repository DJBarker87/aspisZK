#!/usr/bin/env python3
"""SYNTHETIC tests of the evidence gate; NOT performance measurements."""
import copy,json,pathlib,subprocess,sys,tempfile
root=pathlib.Path(__file__).resolve().parents[1]
base={'commit_sha':'a'*40,'elf_sha256':'b'*64,'scope':'complete-primary-verifier','instrumented':False,'heap_bytes':262144,'same_profile':True,'cases':[
 {'kind':'honest','fixture_sha256':'c'*64,'cu':950000,'cu_limit':1000000,'complete':True,'resource_failure':False,'accepted':True},
 {'kind':'honest','fixture_sha256':'d'*64,'cu':960000,'cu_limit':1000000,'complete':True,'resource_failure':False,'accepted':True},
 {'kind':'negative','cu':700000,'cu_limit':1000000,'complete':True,'resource_failure':False,'accepted':False}]}
records=[(base,True)]
for kind in ['old_cu','high_cap','partial','resource','heap','missing_negative','duplicate_fixture','instrumentation']:
 r=copy.deepcopy(base)
 if kind=='old_cu':r['cases'][0]['cu']=3279621
 if kind=='high_cap':r['cases'][0]['cu_limit']=100000000
 if kind=='partial':r['cases'][0]['complete']=False
 if kind=='resource':r['cases'][2]['resource_failure']=True
 if kind=='heap':r['heap_bytes']=524288
 if kind=='missing_negative':r['cases'].pop()
 if kind=='duplicate_fixture':r['cases'][1]['fixture_sha256']=r['cases'][0]['fixture_sha256']
 if kind=='instrumentation':r['instrumented']=True
 records.append((r,False))
with tempfile.TemporaryDirectory() as d:
 p=pathlib.Path(d)/'synthetic.json'
 for r,expected in records:
  p.write_text(json.dumps(r));run=subprocess.run([sys.executable,str(root/'tools/check_budget.py'),str(p)],capture_output=True,text=True)
  got=json.loads(run.stdout);assert got['sub_1m_benchmark_pass']==expected
  assert (run.returncode==0)==expected
print(json.dumps({'synthetic_gate_cases':len(records),'all_passed':True,'SBF_measurements':0}))
