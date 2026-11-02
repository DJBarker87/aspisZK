"""Literal git-grep filename census of every tracked textual reference, all refs containing the model."""
from pathlib import Path
import subprocess,json,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd7-20261102';base=json.load(open(E/'CONSUMERS-census.json'));base['results']=[r for r in base['results'] if r['lean_direct_files']];rows=[]
for row in base['results']:
 rev=row['revision'];out=E/('all-reference-'+rev+'.txt')
 q=subprocess.run(['git','grep','-l','-I','-E','PV_RDCD4_(BytesSource|SliceRange194)',rev,'--'],cwd=R,capture_output=True)
 assert q.returncode in (0,1),(rev,q.stderr)
 out.write_bytes(q.stdout)
 paths=[s[len(rev)+1:] for s in q.stdout.decode().splitlines()]
 rows.append(dict(revision=rev,refs=row['refs'],files=paths,code_files=[p for p in paths if Path(p).suffix in {'.lean','.py','.sh','.rs'}],text_or_evidence_files=[p for p in paths if Path(p).suffix not in {'.lean','.py','.sh','.rs'}]))
 (E/'ALL-REFERENCES-census.json').write_text(json.dumps(dict(scope='Supplemental text/evidence references on all refs containing the model; all other refs already have negative complete executable-source census',command='git grep -l -I -E PV_RDCD4_(BytesSource|SliceRange194) REV --',results=rows,complete=False),indent=2)+'\n')
 print(len(rows),'of',len(base['results']),rev[:10],len(paths),'references',flush=True)
(E/'ALL-REFERENCES-census.json').write_text(json.dumps(dict(scope='Supplemental text/evidence references on all refs containing the model; all other refs already have negative complete executable-source census',command='git grep -l -I -E PV_RDCD4_(BytesSource|SliceRange194) REV --',results=rows,complete=True),indent=2)+'\n')
