import pathlib,re,json
root=pathlib.Path('/home/dombarker/project-offloads');pat=re.compile(r'(?<!\d)(544\d\d)(?!\d)');hits=[]
for job in root.glob('codex-pv-*'):
 for q in job.glob('evidence/**/*'):
  if len(q.relative_to(job).parts)<=6 and q.is_file() and pat.search(q.name):hits.append(str(q))
sent=root/'r1-privacy-build-integration-20261019/evidence/sent.txt';lines=[s for s in sent.read_text().splitlines() if len(s.split())>2 and s.split()[2].isdigit() and 54400<=int(s.split()[2])<=54499]
print(json.dumps(dict(range=[54400,54499],other_receipt_hits=hits,sent_hits=lines,compiler_starts=0,ids_consumed=[]),indent=2))
