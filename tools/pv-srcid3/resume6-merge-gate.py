#!/usr/bin/env python3
"""Produce an explicit fail-closed merge gate for every enumerated import object."""
import pathlib,json
root=pathlib.Path(__file__).resolve().parents[2];e=root/'evidence/pv-srcid3-20261026'
p=json.loads((e/'resume6-project-provenance.json').read_text());pkg=json.loads((e/'resume6-package-closure.json').read_text());project={r['module']:r for r in p['project_modules']}
a=[json.loads(x) for x in (e/'resume6-attempts.jsonl').read_text().splitlines()] if (e/'resume6-attempts.jsonl').exists() else []
lines=['# MERGE GATE: BLOCKED','',f"Research HEAD inspected: `{p['research_revision']}`. Branch base: `92d3db0b2f`.",'','No clean research-HEAD audit is claimed. Attempt 37102 compiled the exact HEAD', '`R1NaturalProjection` source and failed at lines 28 and 58. Five printed axiom', 'reports contain `sorryAx` as a consequence of failed proofs; they are rejected.', 'The pre-existing object is not a research-HEAD output. The source file belongs', 'to the protected soundness cone and was not edited. Its sole direct imported', 'project module and the inspected immediate prerequisites have matching source/', 'object receipts, so this is not evidence of an upstream source repair.', '', 'The full downstream replacement set is in resume6-projection-rebuild-order.json:', '163 objects including the projection itself. No failed unchanged compile is rerun.', '', 'A current host source SHA is deliberately distinguished from the source SHA', 'linked by a successful compile receipt to the current object SHA. Package source', 'copies without a research HEAD source mapping or hash-bearing build receipt are', 'listed as exact provenance gaps. The inventory is recursive across package sources,', 'with implicit Init imports. Missing host sources prevent exhaustive enumeration', 'of their nested imports; those graph gaps are explicit in the JSON inventory.', '', '## Recompiled objects', '']
for r in a:lines.append(f"- {r['attempt']}: `{r['module']}` exit {r['exit']}; source `{r['source_sha256']}`; accepted={r['exit']==0 and not r['nonstandard_axioms']}.")
lines+=['','## Every enumerated imported object','','| Module | Current object SHA-256 | Compiled source SHA = research HEAD SHA, or exact gap |','| --- | --- | --- |']
for r in sorted(pkg['objects'],key=lambda x:x['module']):
 q=project.get(r['module']);obj=r['object_sha256'] or 'MISSING'
 if q:
  expected=q['research_source_sha256'];matches=[x for x in q['object_source_receipts'] if x['object_sha256']==obj]
  if expected and any(x['source_sha256']==expected for x in matches):status=f"`{expected}` = HEAD (receipt {next(x['attempt'] for x in matches if x['source_sha256']==expected)})"
  elif not expected:status=f"GAP: absent from research HEAD; branch source `{q['source_sha256']}`; "+('hash-linked to object' if q['verified_compiled_source_matches_expected'] else 'object/source receipt missing')
  else:status=f"GAP: HEAD `{expected}`; "+('; '.join('receipt source `'+x['source_sha256']+'`' for x in matches) if matches else 'no successful source/object hash link')
 else:status='GAP: no research HEAD source mapping or compiled-source receipt; current host source '+('`'+r['host_source_sha256']+'`' if r['host_source_sha256'] else 'MISSING')
 if r.get('import_graph_gap'):status+='; '+r['import_graph_gap']
 lines.append(f"| `{r['module']}` | `{obj}` | {status} |")
(e/'MERGE-GATE.md').write_text('\n'.join(lines)+'\n')
print('BLOCKED;',len(pkg['objects']),'enumerated imported objects;',len(a),'charged attempts')
