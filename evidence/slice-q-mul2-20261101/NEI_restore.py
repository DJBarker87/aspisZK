from pathlib import Path
import json
def native(p=None):
 assert p is None
 return json.loads((Path(__file__).parent/"NEI_PAYLOAD.json").read_text())
