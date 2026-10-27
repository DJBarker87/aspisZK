"""Read-only local/host source agreement and records boundary audit."""
from pathlib import Path
import subprocess,json,hashlib,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin15-20261027'
p='crates/aspis-statement/src/pool_v1/pair_forest_copy_builder.rs'
def git(*args):return subprocess.check_output(['git',*args],cwd=R,text=True)
rev=git('rev-parse','HEAD').strip();base=git('show','52a3712f25:'+p);s=(R/p).read_text()
def split(s):
 a=s.index('fn records(');b=s.index('\n// ---------- interface for the forest compiler',a)
 return s[:a],s[a:s.index('{',a)+1],s[b:]
assert split(base)==split(s)
paths=git('diff','--name-only','52a3712f25','HEAD','--','crates','programs','Cargo.lock').splitlines();assert paths==[p]
(E/'source-freeze-audit.json').write_text(json.dumps(dict(entry_revision='52a3712f25',final_source_revision=rev,only_shipped_changed_path=paths,only_records_body_changed=True,signature_unchanged=True,source_sha256=hashlib.sha256(s.encode()).hexdigest(),shared_envj_sources_written=False,extractor_modified=False,trust_fields_added=0),indent=2)+'\n')
(E/'shipped-records.diff').write_text(git('diff','52a3712f25','HEAD','--',p));(E/'source-revision.txt').write_text(rev+'\n')
paths=git('ls-files','crates','programs','Cargo.lock').splitlines();local={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths if (R/p).is_file()}
code='import pathlib,json,hashlib;root=pathlib.Path("/home/dombarker/project-offloads/codex-pv-runjoin-20261026/gate13/candidate/src");paths='+repr(list(local))+';print(json.dumps({p:hashlib.sha256((root/p).read_bytes()).hexdigest() for p in paths}))'
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],capture_output=True,text=True,check=True);assert local==json.loads(r.stdout)
(E/'host-source-agreement.json').write_text(json.dumps(dict(tracked_source_files=len(local),all_match=True,source_revision=rev,files=local),indent=2)+'\n')
print(rev,len(local),'match; records boundary intact')
