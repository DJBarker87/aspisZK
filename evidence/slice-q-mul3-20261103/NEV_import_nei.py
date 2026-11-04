"""Execute predecessor checks with generated outputs redirected to own directory.

No proof/validator condition is removed. Only three output locations and the
corresponding generated-module load path change. Imported source stays intact.
"""
from pathlib import Path
import sys,types,hashlib,json
E=Path(__file__).resolve().parent;I=E.parent/'slice-q-mul2-20261101'
sys.dont_write_bytecode=True
sys.path[:0]=[str(I),str(E.parent/'slice-q-compose-20261029')]
def load():
 source=(I/'NEI_composition.py').read_text();adapted=source
 changes={
 "(E/'NEI_NEB_ADDITIVE.py').write_text(added)":"(OUT/'NEV_NEB_ADDITIVE.py').write_text(added)",
 "(E/'NEI_VALIDATOR_SOURCE_DELTA.json').write_text(":"(OUT/'NEV_VALIDATOR_SOURCE_DELTA.json').write_text(",
 "spec_from_file_location('NEI_NEB_ADDITIVE',E/'NEI_NEB_ADDITIVE.py')":"spec_from_file_location('NEV_NEB_ADDITIVE',OUT/'NEV_NEB_ADDITIVE.py')",
 "(E/'NEI_REPLACED_OLD_REGISTRATIONS.json').write_text(":"(OUT/'NEV_REPLACED_OLD_REGISTRATIONS.json').write_text("}
 for old,new in changes.items():
  assert adapted.count(old)==1,old
  adapted=adapted.replace(old,new)
 restored=adapted
 for old,new in changes.items():restored=restored.replace(new,old)
 assert restored==source,'changed inherited check'
 (E/'NEV_NEI_COMPOSITION_ADAPTER.py').write_text(adapted)
 (E/'NEV_NEI_ADAPTER_PROVENANCE.json').write_text(json.dumps(dict(original=str(I.relative_to(E.parent.parent))+'/NEI_composition.py',original_sha256=hashlib.sha256(source.encode()).hexdigest(),adapter_sha256=hashlib.sha256(adapted.encode()).hexdigest(),output_only_replacements=changes,checks_byte_identical=True),indent=2)+'\n')
 module=types.ModuleType('NEV_NEI_READONLY');module.__file__=str(I/'NEI_composition.py');module.OUT=E
 exec(compile(adapted,str(E/'NEV_NEI_COMPOSITION_ADAPTER.py'),'exec'),module.__dict__)
 return module
if __name__=='__main__':
 c=load();base=c.obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json')
 edges=c.prepare(base);out,delta=c.validate(base,edges)
 for name,value in [('NEV_NEI_REPLAY_DELTA.json',delta),('NEV_NEI_REPLAY_EDGES.json',edges),('NEV_NEI_REPLAY_LEDGER.json',out)]:
  (E/name).write_text(json.dumps(value,separators=(',',':'))+'\n')
 print(json.dumps(dict(closed=len(delta['composed_rows_closed']),edges=delta['edge_closed'])))
