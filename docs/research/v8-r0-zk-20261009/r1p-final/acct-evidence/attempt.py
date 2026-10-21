import sys,subprocess,pathlib,hashlib,json,re
root=pathlib.Path(__file__).resolve().parents[2]
a=int(sys.argv[1]); m=sys.argv[2]; host='dombarker@100.108.41.90'
j='/home/dombarker/project-offloads/aspis-joint-20261019'; t='/home/dombarker/project-offloads/aspis-fs-generic-20261006'; h='/home/dombarker/project-offloads/r1-privacy-build-integration-20261019'
src=root/'lean'/f'{m}.lean'
subprocess.run(['scp',str(src),f'{host}:{j}/sources/{m}.lean'],check=True)
imports=re.findall(r'^import (\S+)',src.read_text(),re.M)
code='import hashlib,pathlib; p=pathlib.Path('+repr(j+'/objects')+'); print(hashlib.sha256(";".join(x+"="+hashlib.sha256((p/(x.replace(".","/")+".olean")).read_bytes()).hexdigest() for x in '+repr(sorted(imports))+').encode()).hexdigest()[:16])'
fp=subprocess.check_output(['ssh',host,'python3 -c '+__import__('shlex').quote(code)],text=True).strip()
p=subprocess.run(['ssh',host,f'sh {h}/tools/run-joint.sh {a} {m} J 7000 7 {fp}'],text=True,capture_output=True); print(p.stdout,p.stderr)
out=subprocess.check_output(['ssh',host,f'cat {t}/evidence/out-{a}.log'],text=True)
time=subprocess.check_output(['ssh',host,f'cat {t}/evidence/time-{a}.log'],text=True)
e=pathlib.Path(__file__).parent
(e/f'out-{a}.log').write_text(out); (e/f'time-{a}.log').write_text(time)
def match(p,s):
 r=re.search(p,s); return r.group(1) if r else None
r=dict(attempt=a,module=m,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),deps_fingerprint=fp,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),exit=match(r'exit=(\d+)',out),wall=match(r'Elapsed .*?: (.+)',time),peak_rss_kib=match(r'Maximum resident set size \(kbytes\): (\d+)',time),swaps=match(r'Swaps: (\d+)',time),axioms=re.findall(r"^'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.M),errors=[l for l in out.splitlines() if 'error:' in l])
with (e/'attempts.jsonl').open('a') as f: f.write(json.dumps(r)+'\n')
