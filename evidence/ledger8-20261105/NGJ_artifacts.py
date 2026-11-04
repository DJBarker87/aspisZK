from pathlib import Path
import json,lzma,hashlib,subprocess,re,time,resource
E=Path(__file__).resolve().parent;R=E.parents[1];start=time.monotonic();sha=lambda b:hashlib.sha256(b).hexdigest()
required=['NGJ_LEDGER.md','NGJ_LEDGER.json','NGJ_ROUTES.json','NGJ_TRUST_USED.json','NGJ_COMBINED_IMPORT.lean','NGJ_AUDIT.json','NGJ_SCAN.json','NGJ_CONFLICTS.json','NGJ_STATEMENT.md','NGJ_SHORTEST_PATHS.md','NGJ_HANDOFF.md','NGJ_REMAINING.md','NGJ_ATTEMPTS.jsonl']
for n in required:assert (E/n).is_file() or (E/(n+'.xz')).is_file(),n
assert 'Pending fresh statement' not in (E/'NGJ_STATEMENT.md').read_text()
assert (E/'NGJ_STATEMENT.md').read_text().rstrip().endswith('**target not yet established**')
count=0
for p in E.rglob('*.xz'):
 h=Path(str(p)[:-3]+'.sha256')
 if h.exists():assert sha(lzma.decompress(p.read_bytes()))==h.read_text().strip(),p;count+=1
pack=json.loads((E/'NGJ_PACK.json').read_text())
for r in pack['references']:
 p=E/r['stored_once'];raw=lzma.decompress(p.read_bytes()) if r['encoding']=='xz' else p.read_bytes();assert sha(raw)==r['sha256'] and len(raw)==r['bytes']
rows=[json.loads(l) for l in (E/'NGJ_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rows)==len({r['attempt'] for r in rows})==40
assert {r['attempt'] for r in rows}=={f'NGJ_L{i:03}' for i in range(1,41)}
for r in rows:
 full=json.loads((E/r['full_receipt']).read_text());assert full['attempt']==r['attempt'] and full['exit_status']==r['exit_status']
 assert {'source_revision','source_hashes','deps_fingerprint','wall_seconds','peak_rss_kib','swaps','print_axioms'}<=set(full)
assert not any(p.name=='__pycache__' for p in E.rglob('*'))
assert not any(p.is_file() and p.stat().st_size>20000000 for p in E.rglob('*'))
assert not any(p.is_file() and p.suffix in ['.olean','.o','.ir','.elf','.tar'] for p in E.rglob('*'))
changes=subprocess.check_output(['git','status','--porcelain','-uall'],cwd=R,text=True).splitlines();assert all(l[3:].startswith('evidence/ledger8-20261105/') for l in changes),changes[:5]
host=json.loads((E/'NGJ_HOST_END.json').read_text());assert host['active_owned_provers']==[] and host['key_wallet_actions']==0 and host['exports_checked']==19
result=dict(result='PASS',required_outputs=len(required),compressed_hashes_checked=count,packed_references_checked=len(pack['references']),formal_attempts=40,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),target='NGJ artifact/pin/receipt/size/scope checks',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swap='No prover launch; local Python',print_axioms='N/A; stored raw/print outputs checked by NGJ_finalize.py',proof_launches=0)
(E/'NGJ_ARTIFACTS.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
