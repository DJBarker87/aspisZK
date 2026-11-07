"""Read committed harness sources from the final patch, with exact hash checks."""
from pathlib import Path
import re,json,hashlib
B=Path(__file__).resolve().parent
def moduleText(module):
 pins=json.loads((B/'NMC_PATCH_INPUT_PINS.json').read_text());row=pins[module]
 chunks=re.split(r'(?m)(?=^--- )',(B/'NMC_HARNESSES.patch').read_text())
 matches=[c for c in chunks if c.startswith('--- /dev/null\n+++ b/'+row['path']+'\n')]
 assert len(matches)==1
 body=''.join(line[1:]for line in matches[0].splitlines(keepends=True)if line.startswith('+')and not line.startswith('+++ '))
 assert hashlib.sha256(body.encode()).hexdigest()==row['sha256']
 return body
if __name__=='__main__':
 for module in json.loads((B/'NMC_PATCH_INPUT_PINS.json').read_text()):moduleText(module)
 print('PASS exact patch input hashes')
