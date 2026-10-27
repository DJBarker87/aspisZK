from pathlib import Path
import subprocess,json,hashlib,re
P=Path(__file__).resolve().parent
refs={'research':'HEAD','rw':'codex/cx-prover-rw-20261023','cb':'codex/pv-cb-20261026','cb3':'codex/pv-cb3-20261026','join':'codex/pv-join-20261026','runjoin':'codex/pv-runjoin-20261026','srcid':'codex/pv-srcid3-20261026','rebase':'codex/pv-rebase-20261026','dict':'codex/cx-prover-dict-20261026'}
def git(*a):return subprocess.check_output(['git',*a])
pins={k:git('rev-parse',v).decode().strip() for k,v in refs.items()};(P/'pins.json').write_text(json.dumps(pins,indent=2)+'\n')
manifest=[]
for key,rev in pins.items():
 paths=git('ls-tree','-r','--name-only',rev).decode().splitlines()
 selected=[p for p in paths if (p.endswith('.lean') and ('/lean/R1Z/' in p or '/lean/prover-rw-' in p)) or (p.startswith('evidence/pv-') and p.endswith(('.md','.json')) and any(x in p for x in ['FINAL','final','ROWS','HANDOFF','trust-items','P-before-after','resume-source','RESUME','KANI-CONFIG'])) or (key=='rebase' and ('timing' in p or p=='design/PV-REBASE-20261026.md') and p.endswith(('.json','.md'))) ]
 for path in selected:
  raw=git('show',rev+':'+path); out=P/'snapshots'/key/path
  if path.endswith('.lean'):out=Path(str(out)+'.txt')
  out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(raw)
  manifest.append(dict(ref=key,revision=rev,path=path,sha256=hashlib.sha256(raw).hexdigest(),snapshot=str(out.relative_to(P))))
(P/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('pinned',pins,'captured',len(manifest))
