"""Compose entropy source leaves with the already proved durable entry spine."""
from pathlib import Path
import hashlib,json,sys
src=Path('lean/PV_EVH_DurableProver.lean');s=src.read_text()
s=s.replace('import PV_EVH_AccountGuard','import PV_EVH_AccountFlowEntry')
s=s.replace('namespace PV_EVH_DurableProver','namespace PV_EVH_DurableFlow').replace('end PV_EVH_DurableProver','end PV_EVH_DurableFlow')
s=s.replace('PV_EVH_AccountGuard.entry','PV_EVH_AccountFlowEntry.entry')
s=s.replace('(retryFuel entropyFuel : Nat) (answers : EntropyAnswers)', '(retryFuel entropyFuel : Nat) (answers : EntropyAnswers)\n    (entropy : PV_EVH_EntropyStep.Callees) (nonzero_OPEN : Array U8 32#usize → P Bool)')
s=s.replace('entry inst retryFuel entropyFuel answers public1', 'entry inst retryFuel entropyFuel answers entropy nonzero_OPEN public1')
s=s.replace('entry_OPEN inst retryFuel entropyFuel answers public1', 'entry_OPEN inst retryFuel entropyFuel answers entropy nonzero_OPEN public1')
s=s.replace('    (guard_fixed :', '    (he : PV_EVH_EntropyStep.Compatible entropy)\n    (hn : ∀ n, FinishedView (nonzero_OPEN n) (aspis_prover.state_only_entropy.entropy_nonzero32 n))\n    (guard_fixed :')
s=s.replace('  · exact guard_fixed', '  · exact he\n  · exact hn\n  · exact guard_fixed')
s=s.replace('Inherited entropy afterDraw, nonce helpers, retry-entry comparison op233 and', 'Entropy helpers, nonce helpers, retry-entry comparison op233 and')
p=Path('lean/PV_EVH_DurableFlow.lean');r=Path('evidence/pv-evh5-20261029/durable-flow-generation.json')
record=json.dumps(dict(input=str(src),input_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),output_sha256=hashlib.sha256(s.encode()).hexdigest(),scope='source-spine transport, all native leaves still OPEN; no endpoint closure'),indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==s and r.read_text()==record;print('PASS durable flow generation')
else:p.write_text(s);r.write_text(record)
