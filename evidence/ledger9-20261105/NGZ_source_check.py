from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent;R=E.parents[1];frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
# Sparse directories need not be materialized to compare committed blob IDs.
def tree(rev):
 raw=subprocess.check_output(['git','ls-tree','-r','-z',rev,'--','crates','programs'],cwd=R)
 return {x.split(b'\t',1)[1].decode():x.split(b'\t',1)[0].decode() for x in raw.split(b'\0') if x}
a=tree(frozen);b=tree('HEAD');diff=sorted(k for k in a.keys()|b.keys() if a.get(k)!=b.get(k));dirty=subprocess.check_output(['git','status','--porcelain','--','crates','programs'],cwd=R,text=True).splitlines();assert not diff and not dirty
x=dict(frozen_revision=frozen,head_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),different_tracked_source_paths=diff,dirty_shipped_paths=dirty,no_NGZ_shipped_change=True,elf_rebuild_triggered=False,elf_pins='Inherited only; no ELF rehash/rebuild claimed')
(E/'NGZ_SHIPPED_SOURCE_CHECK.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x))
