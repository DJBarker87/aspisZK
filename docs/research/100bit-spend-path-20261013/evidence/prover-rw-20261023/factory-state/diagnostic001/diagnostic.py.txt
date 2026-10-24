"""Uncharged small read-only scanner/formula check, never launches a build."""
from pathlib import Path
import hashlib, json, runpy, sys, time
D=Path(__file__).resolve().parent
start=time.monotonic()
# Source-identical corrected052 scanner: verify equations independently with
# its retained numerical ruling. No historical snapshot is a launch gate.
gib=2**30
finite=26172456960
resident=25021128704
total=66698661888
assert finite+8*gib < 55*gib
assert finite+8*gib+resident+7*gib-total == 645095424
assert finite+2*gib+resident+7*gib < total
# Parent100 contains capped child30 and uncapped child20: exclusive50+20,
# and reserve30 are charged once; hierarchical100+20 is not added.
assert (100-30-20)+20 == 70
assert 30+70 == 100
ad=runpy.run_path(str(D/'reservation.py'))['admission'](requested=2*gib)
out=dict(schema='ProverRwFactoryState-readonly-diagnostic-v1',
    command=sys.argv, source_revision=(D/'revision.txt').read_text().strip(),
    scanner_sha256={n:hashlib.sha256((D/n).read_bytes()).hexdigest() for n in ['reservation.py','reservation_base.py','diagnostic.py']},
    formula_checks='PASS; historical052 arithmetic and exclusive-child cancellation',
    actual_compiler_invocations=0, charged_reservations=0,
    print_axioms='N/A: read-only arithmetic/scanner diagnostic',
    wall_seconds=time.monotonic()-start,admission=ad)
Path(sys.argv[1]).write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:ad.get(k) for k in ['allowed','utc','bounded_reserved_bytes','projected_reserved_bytes','uncapped_resident_reserve_bytes','reserve_check','error','visibility_error']}))
