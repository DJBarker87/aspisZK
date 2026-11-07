from NMN_batch_client import *
for name in ['NMN_K904','NMN_K905','NMN_K906']:
 x=json.loads((E/(name+'.json')).read_text());rc=batch(x['scope'],x['jobs'])
 if rc['exit_status']:break
 if any((E/j['attempt']/'receipt.json').exists() and json.loads((E/j['attempt']/'receipt.json').read_text()).get('timeout') for j in x['jobs']):break
