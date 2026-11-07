from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();archives=[]
for p in list(E.rglob('*')):
 if p.is_file()and p.stat().st_size>20_000_000:
  b=p.read_bytes();Path(str(p)+'.xz').write_bytes(lzma.compress(b,preset=6));Path(str(p)+'.sha256').write_text(H(b)+'\n');archives.append(dict(path=str(p.relative_to(E)),bytes=len(b),sha256=H(b)));p.unlink()
rows=[json.loads(l)for l in(E/'NNI_ATTEMPTS.jsonl').read_text().splitlines()if '"exit_status"'in l];assert len(rows)==60
fields=['attempt','kind','module','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision']
(E/'NNI_TRANSCRIPT.tsv').write_text('\t'.join(fields+['source_hashes_fingerprint','receipt'])+'\n'+''.join('\t'.join(str(r[k])for k in fields)+'\t'+H(json.dumps(json.loads((E/r['attempt']/'receipt.json').read_text())['source_hashes'],sort_keys=True).encode())+'\t'+r['attempt']+'/receipt.json\n'for r in rows))
(E/'NNI_HYGIENE.json').write_text(json.dumps(dict(archived=archives,files_over20MB=[str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000],one_line_transcripts=60,artifacts_retained=True),indent=1)+'\n')
print('60 one-line scope summaries; large text archived with SHA256')
