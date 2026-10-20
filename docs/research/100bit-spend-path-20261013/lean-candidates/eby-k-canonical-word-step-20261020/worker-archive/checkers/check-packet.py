from pathlib import Path
import hashlib, json
root=Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=(root/'sources/R22CurrentReducerMul.lean').read_text()
new=(root/'sources/EbyKDotPushCanonicalFoldBridgeV1.lean').read_text()
start='def high '
old_block=old[old.index(start):old.index('def wrappingReduce')]
new_block=new[new.index(start):new.index('#print axioms fold_agrees')]
assert old_block==new_block, 'canonical bridge declarations differ from retained R22 declaration/proof text'
assert sha(root/'sources/Funs.lean')=='114552b863f61e970a2ceb4bb048566e4b464b61905c6d7a175f6b117f1aed4a'
assert sha(root/'sources/Types.lean')=='c5a08408bb25ca84fcef1b3689904d27e65510c21775d6db8beeb271fbaa5b15'
assert sha(root/'sources/ExtractedCurrentReducer.lean')=='933ae275dac978bd0ac60035154e5274c4f1a12bffcbc98f2265fbd50e49af74'
for name in ('EbyKDotPushCanonicalFoldBridgeV1','EbyKDotPushActualFoldV2'):
    assert 'sorry' not in (root/'sources'/f'{name}.lean').read_text()
print('PASS: exact high/wrappingFold/fold_agrees body-copy; generated source pins match accepted snapshots; no sorry in new owners')
