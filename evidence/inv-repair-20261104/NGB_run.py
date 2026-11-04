"""Local Python-only ordered evidence regeneration with measured receipts."""
import sys,pathlib,subprocess,time,json,hashlib,re,platform
sys.dont_write_bytecode=True
E=pathlib.Path(__file__).resolve().parent;R=E.parents[1]
revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
attempt_file=E/'NGB_ATTEMPTS.jsonl'
start_number=sum(1 for _ in attempt_file.open())+1 if attempt_file.exists() else 1
for i,name in enumerate(sys.argv[1:] or ['NGB_mir.py','NGB_inventory.py','NGB_slice_build.py','NGB_report.py','NGB_validate.py'],start_number):
 argv=['/usr/bin/time','-l',sys.executable,str(E/name)] if platform.system()=='Darwin' else ['/usr/bin/time','-v',sys.executable,str(E/name)]
 start=time.monotonic();p=subprocess.run(argv,cwd=R,capture_output=True,text=True,env={**__import__('os').environ,'PYTHONDONTWRITEBYTECODE':'1'});wall=time.monotonic()-start
 (E/f'NGB_P{i:03}_stdout.log').write_text(p.stdout);(E/f'NGB_P{i:03}_stderr.log').write_text(p.stderr)
 if platform.system()=='Darwin':
  rss=re.search(r'(\d+)\s+maximum resident set size',p.stderr);swap=re.search(r'(\d+)\s+swaps',p.stderr);unit='bytes'
 else:
  rss=re.search(r'Maximum resident set size \(kbytes\): (\d+)',p.stderr);swap=re.search(r'Swaps: (\d+)',p.stderr);unit='KiB'
 pins={str(q.relative_to(R)):hashlib.sha256(q.read_bytes()).hexdigest() for q in sorted(E.glob('NGB_*.py'))}
 receipt=dict(attempt=f'NGB_P{i:03}',target=name,argv=argv,source_revision=revision,source_sha256=hashlib.sha256((E/name).read_bytes()).hexdigest(),dependency_fingerprint=hashlib.sha256(json.dumps(pins,sort_keys=True).encode()).hexdigest(),script_pins=pins,input_MIR_pins=json.loads((E/'NGB_MIR_EDGES.json').read_text())['inputs'],exit=p.returncode,wall_seconds=wall,peak_RSS=int(rss[1]) if rss else None,peak_RSS_unit=unit,swaps=int(swap[1]) if swap else None,axioms='N/A: Python inspection/producer, no new Lean theorem',compiler_scopes=0)
 with (E/'NGB_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(receipt)+'\n')
 print(name,p.returncode,p.stdout.strip()[:1000],flush=True)
 if p.returncode:print(p.stderr);sys.exit(p.returncode)
