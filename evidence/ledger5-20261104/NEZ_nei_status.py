"""Isolated unchanged NEI replay, redirecting its generated metadata only.

The generated Python validator must equal its already committed source exactly.
This process prevents NEI's global registration hooks leaking into other lanes.
"""
from pathlib import Path
import contextlib,json,sys
from unittest.mock import patch
import NEZ_validate as v
allowed={'NEI_NEB_ADDITIVE.py','NEI_VALIDATOR_SOURCE_DELTA.json','NEI_REPLACED_OLD_REGISTRATIONS.json'}
original=Path.write_text

def retain(self,data,*args,**kwargs):
    assert self.parent == v.R/'evidence/slice-q-mul2-20261101' and self.name in allowed, 'unexpected predecessor write: '+str(self)
    if self.suffix=='.py':assert self.read_text()==data,'generated validator differs from committed source'
    return original(v.E/('NEZ_'+self.name),data,*args,**kwargs)

with patch.object(Path,'write_text',retain):
    import NEI_validate as nei
    nei.main()
print(json.dumps(dict(closed=v.closed(v.read(nei.E/'NEI_DERIVED_LEDGER.json')),prover_runs=0)))
