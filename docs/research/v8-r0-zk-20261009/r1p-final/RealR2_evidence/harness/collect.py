from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent.parent
H='/home/dombarker/project-offloads/codex-cx-real-r2-20261023'
T='/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence'
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
for target in ['RealR2_context_v1','RealR2_seed_v1','RealR2_scalar_contract_v1']:
 d=E/'native-receipts'/target;d.mkdir(parents=True,exist_ok=True)
 for f in ['stdout.log','stderr.log','time.log','receipt.json']:
  subprocess.run(['scp',f'dombarker@100.108.41.90:{H}/receipts/{target}/{f}',str(d/f)],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
 subprocess.run(['scp',f'dombarker@100.108.41.90:{H}/{target}-reservations.json',str(d/'reservations.json')],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
for snapshot in (E/'lean'/'sources').glob('attempt-*.lean.txt'):
 if '-executed-' in snapshot.name:continue
 a=snapshot.name.split('-')[1];d=E/'lean'/a;d.mkdir(exist_ok=True)
 for f in ['out','time','sha']:
  ext='txt' if f=='sha' else 'log'
  subprocess.run(['scp',f'dombarker@100.108.41.90:{T}/{f}-{a}.{ext}',str(d/f'{f}.{ext}')],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
 subprocess.run(['scp',f'dombarker@100.108.41.90:{H}/lean-{a}.json',str(d/'inputs.json')],stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
 if not (d/'out.log').exists():continue
 out=(d/'out.log').read_text();tim=(d/'time.log').read_text() if (d/'time.log').exists() else ''
 record=json.loads((d/'inputs.json').read_text())
 if record['source_sha256'] != hashlib.sha256(snapshot.read_bytes()).hexdigest():
  record['upload_race_diagnostic']=True
  snapshot=E/'lean'/'sources'/('attempt-'+a+'-executed-context.lean.txt')
  assert record['source_sha256']==hashlib.sha256(snapshot.read_bytes()).hexdigest()
 meta=json.loads(snapshot.with_suffix('.metadata.json').read_text())
 record.update(source_revision=meta['source_revision'],source_snapshot=str(snapshot.relative_to(E)),source_sha256=hashlib.sha256(snapshot.read_bytes()).hexdigest(),axioms_lines=[l for l in out.splitlines() if 'depends on axioms' in l],exit_status=int(re.search(r'^exit=(\d+)',out,re.M)[1]) if re.search(r'^exit=(\d+)',out,re.M) else None,wall=next((l.strip() for l in tim.splitlines() if 'Elapsed' in l),None),peak_rss_kib=int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',tim)[1]) if 'Maximum resident' in tim else None,swaps=int(re.search(r'Swaps: (\d+)',tim)[1]) if 'Swaps:' in tim else None)
 (d/'evidence.json').write_text(json.dumps(record,indent=2)+'\n')
