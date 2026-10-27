from pathlib import Path
import os,json,hashlib
T=Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence');U=Path('/home/dombarker/project-offloads/codex-cx-import-union-20261022');records=[]
for name in ['EJS_formatter_joint','EJS_formatter_union']:
 root=U/name/'objects'
 for p in list((root/'Aeneas').rglob('*'))+list(root.glob('Aeneas.*'))+list(root.glob('AeneasMeta.*')):
  if p.is_symlink() and p.is_file():
   source=p.resolve();h=hashlib.sha256(p.read_bytes()).hexdigest();p.unlink();os.link(source,p);records.append(dict(path=str(p),source=str(source),sha256=h))
p=U/'EJS_formatter_joint/sources/EJS_FmtAudit.lean';p.write_bytes((T/'EJS_FmtAudit.lean').read_bytes())
rows=json.loads((T/'EJS_formatter-sources.json').read_text());rows.append(dict(workspace='EJS_formatter_joint',module='EJS_FmtAudit',host_path=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),revision='EJS diagnostic source',blob='new EJS_FmtAudit.lean; no theorem',bytes=p.stat().st_size))
(T/'EJS_formatter-sources.json').write_text(json.dumps(rows,indent=2)+'\n')
(T/'EJS_formatter-loader-repair.json').write_text(json.dumps(dict(reason='31019/31020 still loaded legacy Formatter through canonical cache paths. Replace object aliases with hardlinks; no object bytes edited. Probe actual declaration before retrying consumers.',bindings=records),indent=2)+'\n');print('hardlinked',len(records),'objects; diagnostic staged')
