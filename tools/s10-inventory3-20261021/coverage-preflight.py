#!/usr/bin/env python3
"""Check actual Site/Cone compatibility before generating a coverage claim."""
import hashlib,json,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013';E=B/'evidence/s10-inventory3-20261021'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
core=B/'lean/OraclePortJoinSplitCore.lean';owners={r['name']:r['owner'] for r in json.loads((B/'evidence/s10-inventory2-20261021/mir-owners.json').read_text())}
cones={*('S'+str(i) for i in range(1,10)),'parser/codec','multiproof','checkpoint ABI','Pool caller'}
rows=json.loads((E/'affected-declarations.json').read_text());unlowered=[dict(id=r['id'],declaration=r['declaration'],owner=owners[r['declaration']]) for r in rows if owners[r['declaration']] not in cones]
result=dict(schema='s10-coverage-preflight-v1',target='OraclePortJoinSplit.Site / Cone',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),core_sha256=sha(core),declarations=len(rows),site_compatible_owner_labels=len(rows)-len(unlowered),unlowered_caller_declarations=unlowered,
 exit_status=2 if unlowered else 0,lean_compiler_invoked=False,
 print_axioms='N/A: no new Lean theorem or coverage instance. Original four model-only audits reused in validation.json.',
 obstruction='A Site requires owner : Cone. ordered caller join is not a Cone constructor. This does not show source coverage is impossible: caller lowering may represent the helper inside another site or the caller, but that lowering and its semantics must be supplied. Dropping the record or choosing an arbitrary Cone would not prove the final source inventory.',
 additional_obligations='Even an owner-compatible list would not construct the source tree, its signature and mutable/error carriers, source_order or model_order. The 40 affected source records are not the complete deployed declaration list.')
(E/'coverage-preflight.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result));raise SystemExit(result['exit_status'])
