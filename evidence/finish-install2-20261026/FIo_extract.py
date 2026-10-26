from pathlib import Path
import json,subprocess,sys,time
P=Path(__file__).resolve().parent;R=P.parents[1];B='/home/dombarker/project-offloads/codex-cx-sound-int2-20261025';H='dombarker@100.108.41.90'
a,kind,target=sys.argv[1:]; attempt='FIo_'+a
base=json.loads((R/'evidence/finish-install-20261026'/('FIn_C006.json' if kind=='charon' else 'FIn_A006.json')).read_text())
base['attempt']=attempt;base['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
if kind=='charon':
 base['sources']=[str(x.relative_to(P)) for x in sorted((P/'FIo_PairKit').rglob('*')) if x.is_file()]
 base['command']=[x.replace('FIn_PairKit','FIo_PairKit').replace('FIn_pair_owned',target).replace('FIn_PairSplit.llbc',target+'.llbc') for x in base['command']]
 base['env']['CARGO_TARGET_DIR']=B+'/FIo_charon_target'
 if target=='grouped':
  base['command']=[x.replace('crate::weights::grouped','crate::FIo_reference::grouped') for x in base['command']]
  k=base['command'].index('--start-from');base['command'][k:k]=['--include','crate::FIo_reference']
else:
 base['sources']=[target+'.llbc'];base['command']=[x.replace('FIn_PairExtract','FIo_PairExtract').replace('FIn_pair_split_generated','FIo_'+target+'_generated').replace('FIn_PairSplit.llbc',target+'.llbc') for x in base['command']]
base['expected_time']='Focused extraction isolation: '+target+'; compilation/translation, no arithmetic aggregation'
(P/(attempt+'.json')).write_text(json.dumps(base,indent=2)+'\n')
barrier='python3 /home/dombarker/project-offloads/codex-cx-s2c-20261023/reservation.py '+B+'/'+attempt+'-reservation.json'
for i in range(11):
 p=subprocess.run(['ssh',H,barrier+' > '+B+'/'+attempt+'-barrier.log 2>&1; s=$?; cat '+B+'/'+attempt+'-barrier.log; exit $s'],capture_output=True,text=True)
 (P/(attempt+'-barrier.log')).write_text(p.stdout+p.stderr)
 if p.returncode==0:break
 if p.returncode==78 and i<10: print('Reservation busy',flush=True);time.sleep(180);continue
 if 'FileNotFoundError' in p.stdout+p.stderr and i==0:time.sleep(30);continue
 sys.exit(p.returncode)
if kind=='charon':subprocess.run(['scp','-qr',str(P/'FIo_PairKit'),H+':'+B+'/'],check=True)
subprocess.run(['scp','-q',str(P/(attempt+'.json')),H+':'+B+'/'],check=True)
p=subprocess.run(['ssh',H,'cd '+B+' && systemd-run --user --scope -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 S2W_run_host.py '+attempt+'.json'],capture_output=True,text=True)
print(p.stdout+p.stderr)
subprocess.run(['scp','-qr',H+':'+B+'/'+attempt,str(P)],check=True)
subprocess.run(['scp','-q',H+':'+B+'/'+attempt+'-reservation.json',str(P)],check=True)
sys.exit(p.returncode)
