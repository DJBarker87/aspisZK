from run import H,run
import json,sys
old,new=sys.argv[1:];p=H/old
assert not (p/'receipt/receipt.json').exists(),'an admitted run must never be blindly retried'
assert (p/'refusal.json').exists() or (p/'cooldown-refusal.json').exists() or (p/'barrier.json').exists()
x=json.loads((p/'target.json').read_text())
sys.exit(run(new,x['command'],x['expected_time']))
