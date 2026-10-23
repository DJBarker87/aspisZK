from pathlib import Path
import hashlib,json,sys
assert len(sys.argv)==3, 'usage: check_adapter.py ORIGINAL_ALIAS2.lean PURE_IDENTITY.lean'
old=Path(sys.argv[1]).read_text();new=Path(sys.argv[2]).read_text()
end=old.index('\n\n/-- The same accepted native push')
expected=old[:end].replace('import S9ActualEbyKPushSourceV1\nimport S5QRaw.EbyKPushDecodedProductUpdateV1','import S9ActualRawNativeOperandsV1').replace('AspisR1S9ActualEbyKRawAliasV1','AspisR1S9ActualRawHookIdentityV1').replace('AspisR1EbyKPushDecodedProductUpdate.QRaw','AspisR1CanonicalQRawUnified.canonical.Q.raw')
expected+='\n#print axioms actual_raw_eq_source\nend AspisR1S9ActualRawHookIdentityV1\n'
assert expected==new, 'Unexpected pure identity proof/body alteration'
print('PASS: exact existing four equality leaves and pure identity; unrelated consumer removed')
