#!/usr/bin/env python3
"""PCWC_s1_compare.py EMITTED_FUNS: apply the four mechanical post-processing steps to a fresh Funs emission and compare to the committed S1ValuesOwnedModelV1.lean."""
import sys,subprocess,hashlib,json,difflib
sys.dont_write_bytecode=True
sha=lambda b:hashlib.sha256(b).hexdigest()
fresh=open(sys.argv[1],'rb').read().decode()
gate=subprocess.check_output(['git','show','research:evidence/port17release-20261024/dependency-source/S1ValuesOwnedModelV1.lean']).decode()
t=fresh
steps=[]
def rep(a,b,name,count=None):
    global t
    n=t.count(a);steps.append(dict(step=name,occurrences=n));t=t.replace(a,b)
rep('import AspisS1ValuesOwned.Types\n','import S1ValuesOwnedTypesV1\n','T1 import of the Types module renamed to the gate module name')
rep('set_option maxHeartbeats 1000000\n','','T2 delete Aeneas default maxHeartbeats line')
rep('set_option maxRecDepth 2048\n','','T2 delete Aeneas default maxRecDepth line')
rep('core.result.Result.Err CodecError.Length','core.result.Result.Err AspisR1CurrentCaller.compact.CodecError.Length','T3 qualify the CodecError constructor with the frozen-extraction type')
rep('\nend AspisS1ValuesOwned','\n#print axioms read_input\n#print axioms write_output\n#print axioms copy_chunk\n#print axioms values_owned_reference\nend AspisS1ValuesOwned','T4 add #print axioms lines')
res=dict(fresh_sha256=sha(fresh.encode()),gate_sha256=sha(gate.encode()),transformed_sha256=sha(t.encode()),identical_after_transform=(t==gate),steps=steps,
 raw_diff=''.join(difflib.unified_diff(gate.splitlines(1),fresh.splitlines(1),'gate','fresh')),
 residual_diff=''.join(difflib.unified_diff(gate.splitlines(1),t.splitlines(1),'gate','transformed')))
json.dump(res,open(sys.argv[2],'w'),indent=1)
print(res['identical_after_transform'],res['transformed_sha256'],res['gate_sha256'])
