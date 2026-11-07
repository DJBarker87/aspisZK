"""Reviewable source snapshots; replay retains every original Rust harness name."""
from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
index=json.loads((E/'NMM_INPUTS.json').read_text());parts=[];rows=[]
for attempt,files in sorted(index['attempts'].items()):
 if not attempt.startswith('NMM_K') or attempt=='NMM_K001':continue
 for name,h in sorted(files.items()):
  if Path(name).name not in ['NMM_bl_lane.rs','NMM_bl_registry.rs','NMM_legacy.rs','NMM_order.rs']:continue
  raw=lzma.decompress((E/index['objects'][h]['path']).read_bytes());assert hashlib.sha256(raw).hexdigest()==h
  text=raw.decode();dest='NMM_replay/'+attempt+'/'+name
  parts.append('diff --git a/'+dest+' b/'+dest+'\nnew file mode 100644\n--- /dev/null\n+++ b/'+dest+'\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in text.splitlines()))
  cfg=json.load(open(E/(attempt+'.json')))
  rows.append(dict(attempt=attempt,path=dest,source_sha256=h,target=cfg['module'],native_command=cfg['native_command'],scope='Scratch-only cfg(kani) overlay; original Rust identifiers retained; replay via archived NMM_INPUTS and owned runner'))
manifest=json.dumps(dict(frozen_verifier='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',pool='b936275465',snapshots=rows),indent=1)+'\n'
dest='NMM_replay/NMM_INDEX.json'
parts.append('diff --git a/'+dest+' b/'+dest+'\nnew file mode 100644\n--- /dev/null\n+++ b/'+dest+'\n@@ -0,0 +1,'+str(len(manifest.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in manifest.splitlines()))
p=E/'NMM_HARNESSES.patch';p.write_text(''.join(parts));h=hashlib.sha256(p.read_bytes()).hexdigest()
p.with_suffix(p.suffix+'.sha256').write_text(h+'  '+p.name+'\n')
(E/'NMM_HARNESS_INDEX.json').write_text(manifest)
print(json.dumps(dict(snapshots=len(rows),patch_bytes=p.stat().st_size,patch_sha256=h)))
