from pathlib import Path
import json,base64,lzma,hashlib,tarfile,io
E=Path(__file__).resolve().parent
roots=json.loads((E/'NJX_AUDIT_ROOTS.json').read_text())['roots'];results=[];archives=[]
for i in range(42):
 D=E/'NJX_audit_gate2'/f'proof{i}';r=json.loads((D/'receipt.json').read_text());assert r['exit_status']==0 and r['standard_only'];results+=r['results']
 out=D/'NJX_raw.tar.xz'
 if not out.exists():
  with tarfile.open(out,'w:xz')as t:
   for f in sorted(D.glob('*.xz.b64.txt')):
    packed=base64.b64decode(f.read_text());raw=lzma.decompress(packed);original=f.name[:-len('.xz.b64.txt')];h=D/(original+'.sha256');assert hashlib.sha256(raw).hexdigest()==h.read_text().strip()
    for name,data in [(original+'.xz',packed),(h.name,h.read_bytes())]:
     info=tarfile.TarInfo(name);info.size=len(data);info.mtime=0;t.addfile(info,io.BytesIO(data))
  assert out.stat().st_size<20_000_000
  for f in D.glob('*.xz.b64.txt'):
   original=f.name[:-len('.xz.b64.txt')];(D/(original+'.sha256')).unlink();f.unlink()
 digest=hashlib.sha256(out.read_bytes()).hexdigest();out.with_suffix(out.suffix+'.sha256').write_text(digest+'\n');archives.append(dict(path=str(out.relative_to(E)),sha256=digest,bytes=out.stat().st_size))
assert len(results)==len(roots)==9435 and {x['root']for x in results}==set(roots) and len({x['root']for x in results})==len(results)
assert all(x['equal'] and set(x['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for x in results)
scan=json.loads((E/'NJX_audit_gate2/scan/receipt.json').read_text());assert scan['exit_status']==0 and not any(scan[k]for k in ['dangling','duplicate_owners','import_mismatch'])
fixtures=json.loads((E/'NJX_audit_gate2/fixtures/receipt.json').read_text());assert fixtures['fixture_pass']
rows=[json.loads(l)for l in (E/'NJX_ATTEMPTS.jsonl').read_text().splitlines()];counts={k:sum(x['attempt'][4]==k for x in rows)for k in ['L','K','E']};assert counts==dict(L=120,K=32,E=0),counts
for n in [150,151,149]:assert json.loads((E/f'NJX_L{n}/receipt.json').read_text())['exit_status']==0
x=dict(status='PASS_NEXT_LEDGER_GATE',target_established=False,headline='AspisR1.RPx_Deployed.deployed',raw_roots=len(results),all_equal=True,standard_axioms_only=True,scan=scan,fixtures_receipt='NJX_audit_gate2/fixtures/receipt.json',same_binary_pins='NJX_LINK.json',combined_attempts=['NJX_L104','NJX_L150'],combined_count=2,first_scan_failure='NJX_GATE1.json',second_scan='NJX_L151',archives=archives,budget_used=counts,budget_authorized=dict(L=120,K=70,E=0),native_rejected=['NJX_K021','NJX_K022'],native_pairs='NJX_NATIVE_PAIRS.json',remaining='NJX_REMAINING.md',trust='P6/D188 option A reclassification; no added trust rows',credit_waits_next_ledger_gate=True)
(E/'NJX_AUDIT.json').write_text(json.dumps(x,indent=1))
for name in ['NJX_CLOSED.json','NJX_LEDGER_DELTA.json']:
 p=E/name;x=json.loads(p.read_text())
 if 'functions'in x:
  for f in x['functions']:f['local_gate']='PASS_NEXT_LEDGER_GATE'
 else:x['local_gate']='PASS_NEXT_LEDGER_GATE'
 p.write_text(json.dumps(x,indent=2)+'\n')
print('PASS:9435 unique raw roots; standard axioms; NFX zero findings;120 Lean/support,32 Kani;five candidates await ledger')
