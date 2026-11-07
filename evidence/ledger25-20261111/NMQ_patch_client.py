from pathlib import Path
E=Path(__file__).resolve().parent
p=E/'NMQ_HypothesisReview.lean';s=p.read_text().replace('#print NMN_064.G\n','').replace('#print NMN_064.Law\n','#print NLW_Full064.Law\n').replace('NMN_Headline.root0_or_collision','NMN_Headline.accepted_occurrence');p.write_text(s)
p=E/'NMQ_setup.py';s=p.read_text();s=s.replace("cache_imports", "cache_imports")
# Seed the identical raw audit executable and C walker; not a new link.
needle="w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')"
s=s.replace(needle,"""native=b/'NMQ_native';native.mkdir(exist_ok=True)
source=Path('/home/dombarker/project-offloads/codex-cx-ledger24-20261110/NLX_native/NLX_ProofDriver')
shutil.copy2(source,native/'NMQ_ProofDriver')
rows.append(dict(tag='raw-ax2-binary',path=str(source),destination=str(native/'NMQ_ProofDriver'),sha256=hashlib.sha256(source.read_bytes()).hexdigest(),bytes=source.stat().st_size))
"""+needle)
p.write_text(s)
p=E/'NMQ_batch.py';s=p.read_text();s=s.replace("B=Path.cwd();mode=sys.argv[1];", """B=Path.cwd();mode=sys.argv[1];
# The unchanged binary has legacy manifest names baked in; these are private input aliases only.
for n in ['AUDIT_ROOTS.json','AUDIT_MODULES.json']:
 (B/('NLX_'+n)).write_bytes((B/('NMQ_'+n)).read_bytes())
""")
p.write_text(s)
# audit needs no unused ProofDriver source; obtain exact binary pin for each scope.
p=E/'NMQ_run.py';s=p.read_text();p.write_text(s)
