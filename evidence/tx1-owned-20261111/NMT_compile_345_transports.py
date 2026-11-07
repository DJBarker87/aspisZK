from NMT_formal import run,E
import json
mods=['NMT_345TransportBase']+[x['module']for x in json.loads((E/'NMT_345_TRANSPORTS.json').read_text())]
for n,m in enumerate(mods,89):
 if (E/f'NMT_L{n:03}'/'receipt.json').exists():continue
 r=run(f'NMT_L{n:03}','lean',m)
 if r['exit_status']:break
