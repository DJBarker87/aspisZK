"""Repair own source-derived import lists: Lean adds Init unless prelude."""
from pathlib import Path
import json,re,hashlib
E=Path(__file__).resolve().parent;old=(E/'NGZ_EXPECTED_IMPORTS.jsonl').read_text();b={r['module']:r['imports']for r in map(json.loads,old.splitlines())};rows=[json.loads(l)for l in (E/'NGZ_LOADED_scan.jsonl').read_text().splitlines()]
(E/'NGZ_INITIAL_LOADED_scan.jsonl').write_bytes((E/'NGZ_LOADED_scan.jsonl').read_bytes());(E/'NGZ_INITIAL_EXPECTED_IMPORTS.jsonl').write_text(old)
changes=[]
for pre in ['NGK','NGC','NGN','NGO','NGV','NGM','NGT','NGU','NGH','NGD','NFW','NGP','NGR','NGS','NGZ']:
 d=E if pre=='NGZ'else next(E.parent.glob('*/'+pre+'_HANDOFF.md')).parent
 for p in d.glob(pre+'_*.lean'):
  source=p.read_text();imports=re.findall(r'^import ([\w.]+)',source,re.M)
  expected=list(dict.fromkeys(([]if re.search(r'^prelude\b',source,re.M)else['Init'])+imports))
  if b.get(p.stem)!=expected:changes.append(dict(module=p.stem,source=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),before=b.get(p.stem),after=expected));b[p.stem]=expected
# Diagnostic only: verify original defects are exactly this own parser omission.
bad=[r for r in rows if not r['imports_match']]
assert len(bad)==327 and all(not r['dangling']and not r['duplicate_owners']for r in rows)
assert all(b[r['module']]==r['imports']for r in bad)
(E/'NGZ_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(b.items())))
(E/'NGZ_BASELINE_REPAIR.json').write_text(json.dumps(dict(reason='Own source parser omitted implicit Init. No forest/object/driver/walker change; independent source lists use normal Lean default prelude.',initial_attempt='NGZ_L033',initial_missing_Init=327,initial_dangling=0,initial_incompatible_owners=0,changes=changes,derived_from_scan=False,changed_inputs_only=True),indent=1)+'\n')
