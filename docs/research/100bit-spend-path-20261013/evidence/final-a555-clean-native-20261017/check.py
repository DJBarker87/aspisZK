#!/usr/bin/env python3
"""Hash/receipt/native trace audit only; no builds or runtime execution."""
from pathlib import Path
import hashlib,json,re,subprocess,tarfile,io
ROOT=Path(__file__).resolve().parents[5];E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/final-a555-clean-native-20261017'
sha=lambda b:hashlib.sha256(b).hexdigest()
s=json.loads((E/'SUMMARY.json').read_text());archive=E/'final-a555-clean-native.tar.gz';assert sha(archive.read_bytes())==s['archive_sha256']
with tarfile.open(archive) as t:
 for n in ['inputs-clean.json']:
  d=json.load(t.extractfile(n))
  for path,digest in d['files'].items():assert sha(t.extractfile(path).read())==digest,(n,path)
 clean=json.load(t.extractfile('inputs-clean.json'))
 gitpins=json.load(t.extractfile('worker-a-final-a555-source-files.json'))
 git_archive=subprocess.check_output(['git','-C',str(ROOT),'archive','--format=tar',s['revision'],*gitpins])
 with tarfile.open(fileobj=io.BytesIO(git_archive))as git:
  blobs={q.name:git.extractfile(q).read()for q in git if q.isfile()}
 assert set(blobs)==set(gitpins)
 for relative,digest in gitpins.items():
  assert sha(blobs[relative])==digest==clean['files']['source-clean/'+relative],relative
 codec=t.extractfile('runs/codec1233-final/stdout.log').read()
 assert codec==t.extractfile('baseline/codec1233.stdout.log').read()
 assert re.findall(rb'^case (\d+)$',codec,re.M)==[str(i).encode() for i in range(1233)]
 assert codec.endswith(b'complete 1233\n')
 before=json.load(t.extractfile('baseline/ordered-counter.json'))
 after=json.load(t.extractfile('ordered-counter.json'))
 assert before['ordered_digest_calls']==after['ordered_digest_calls']
 assert len(after['ordered_digest_calls'])==583
 assert before['acceptance']==after['acceptance']
 for key in before['fixture']:
  if key not in ['proof_path','public_path']:assert before['fixture'][key]==after['fixture'][key],key
 for key,value in before['hash_input_counts'].items():
  current=after['hash_input_counts'][key]
  if key=='repeated_exact_inputs':
   # This report inventory is produced by HashMap iteration. The actual digest
   # call sequence above is compared verbatim and is never sorted.
   assert sorted(value,key=lambda q:q['input_hex'])==sorted(current,key=lambda q:q['input_hex'])
  else:assert value==current,key
 assert after['hash_input_counts']['tx1_raw_calls']==349
 assert after['hash_input_counts']['tx2_raw_calls']==234
 names=lambda raw:re.findall(rb'^test (\S+) \.\.\. ok$',raw,re.M)
 checkpoint=names(t.extractfile('runs/checkpoint23-final/stdout.log').read())
 assert len(checkpoint)==23 and set(checkpoint)==set(names(t.extractfile('baseline/checkpoint.stdout.log').read()))
 for label,r in s['results'].items():
  actual=json.load(t.extractfile('runs/'+label+'/receipt.json'));assert actual==r and r['exit_status']==0
  assert r['process_swaps']==0 and r['limits']['memory.swap.max']=='0'
  assert sha(t.extractfile('runs/'+label+'/stdout.log').read())==r['stdout_sha256']
  assert sha(t.extractfile('runs/'+label+'/stderr.log').read())==r['stderr_sha256']
print(json.dumps({"status":"PASS","clean_gates":3,"codec_cases_exact":1233,"ordered_calls_exact":583,"tx1_calls":349,"tx2_calls":234,"checkpoint_tests":23,"builds_executed":False}))
