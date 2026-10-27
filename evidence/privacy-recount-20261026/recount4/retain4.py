from pathlib import Path
import json
P=Path(__file__).resolve().parent
used={tuple(x) for x in json.loads((P/'used-sources4.json').read_text())}
audit=json.loads((P/'definition-audit4.json').read_text())
for row in audit:
 for x in row['sources']:used.add((x['ref'],x['path']))
# Preserve all cited evidence documents, but don't vendor thousands of unchanged Lean sources.
manifest=json.loads((P/'manifest.json').read_text());retained=[]
for x in manifest:
 if (x['ref'],x['path']) in used or x['path'].endswith('.md'):retained.append(x)
blobs={x['blob'] for x in retained};removed=0
for f in (P/'objects').glob('*.txt'):
 if f.stem not in blobs:f.unlink();removed+=1
(P/'manifest.json').write_text(json.dumps(retained,indent=2)+'\n')
(P/'retention4.json').write_text(json.dumps(dict(manifest_before=len(manifest),manifest_after=len(retained),source_objects_retained=len(blobs),redundant_local_text_snapshots_removed=removed,authority='Pinned git blobs remain authoritative; no source repository or sibling file deleted'),indent=2)+'\n')
print('Retained source records',len(retained),'unique text snapshots',len(blobs),'removed redundant local snapshots',removed)
