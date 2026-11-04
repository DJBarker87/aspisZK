from pathlib import Path
import os,json,subprocess,hashlib
B=Path(__file__).resolve().parent;os.chdir(B)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
p=json.load(open('PLAN.json'));a=91390
assert not Path(f'attempt-{a}.json').exists()
assert sha(p['sysroot']+'/bin/lean')==json.load(open('NER_STREAM_B_COHORT_META.json'))['lean_binary_sha256']
cfg=dict(kind='lean',module='PV_NER_Scan',attempt=f'lean-{a}',sources=['PV_NER_Scan.lean'],env=dict(LEAN_PATH=p['LEAN_PATH']),timeout=600,command=[p['sysroot']+'/bin/lake','env','lean','-j1','-M7000','-DElab.async=false','-o','PV_NER_Scan.olean','PV_NER_Scan.lean'],source_revision=json.load(open('AUTHORITY.json'))['workspace_revision'],deps_fingerprint=dict(lean_binary_sha256=sha(p['sysroot']+'/bin/lean'),scanner_method='NER_FinalDriverV2 referenceNames + loadedScan; compile helper only'),expected_time='focused scanner helper compilation; no combined closure import')
Path(f'attempt-{a}.json').write_text(json.dumps(cfg,indent=2)+'\n')
with open(f'admission-{a}.log','w') as log:r=subprocess.run(['python3',str(B.parent/'codex-pv-runjoin-20261026/reservation-existing.py'),f'admission-{a}.json'],stdout=log,stderr=subprocess.STDOUT)
assert r.returncode==0 and json.load(open(f'admission-{a}.json'))['allowed'] is True
with open(f'launch-{a}.log','w') as log:r=subprocess.run(['systemd-run','--user','--scope','--quiet',f'--unit=pv-evhc6-{a}','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(B/'S2W_run_host.py'),f'attempt-{a}.json'],stdout=log,stderr=subprocess.STDOUT)
print(Path(f'lean-{a}/stdout.log').read_text());raise SystemExit(r.returncode)
