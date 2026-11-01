"""Expose retry-entry comparison as unfinished, rather than erase its effects."""
from pathlib import Path
import hashlib,json,sys
src=Path('lean/PV_EVH_AccountEntry.lean');s=src.read_text()
s=s.replace('PV_EVH_AccountEntry','PV_EVH_AccountGuard')
s=s.replace('(prove_OPEN : ProveP)', '(prove_OPEN : ProveP)\n    (guard_OPEN : transport.Variant → P Bool)')
s=s.replace('let b ← PV_EVH_Prefix.lift (core.cmp.PartialEq.ne.trait_default\n    transport.Variant.Insts.CoreCmpPartialEqVariant variant transport.Variant.S2)', 'let b ← guard_OPEN variant')
s=s.replace('account account_OPEN prove_OPEN','account account_OPEN prove_OPEN guard_OPEN')
s=s.replace('    (same :', '    (guard_fixed : ∀ v, FinishedView (guard_OPEN v)\n      (core.cmp.PartialEq.ne.trait_default transport.Variant.Insts.CoreCmpPartialEqVariant v transport.Variant.S2))\n    (same :')
s=s.replace('· exact PV_EVH_Prefix.lift_fixed _','· exact guard_fixed variant',1)
s=s.replace('prove_OPEN same account_fixed prove_fixed','prove_OPEN guard_OPEN guard_fixed same account_fixed prove_fixed')
s=s.replace('/-- Exact retry-entry guard and actual callback. Masked proving remains OPEN. -/', '/-- Comparison op233/trait-default is explicitly unfinished. It can emit events\nor exhaust before the actual callback; no Result-only effect credit is taken. -/')
p=Path('lean/PV_EVH_AccountGuard.lean');r=Path('evidence/pv-evh5-20261029/account-guard-generation.json')
record=json.dumps(dict(input=str(src),input_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(s.encode()).hexdigest(),unfinished='core.cmp.PartialEq.ne.trait_default transport.Variant.Insts.CoreCmpPartialEqVariant (op233)',scope='source entry erasure only; guard native interpretation remains OPEN'),indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==s and r.read_text()==record;print('PASS account guard generation')
else:p.write_text(s);r.write_text(record)
