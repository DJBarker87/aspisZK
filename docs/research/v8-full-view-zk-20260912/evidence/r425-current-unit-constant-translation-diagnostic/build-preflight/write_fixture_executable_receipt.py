"""PREPARED READ-ONLY POSTBUILD HASH CENSUS; never edits build/result.json."""
import hashlib,json,pathlib,sys
ROOT=pathlib.Path('/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a')
BUILD=ROOT/'candidate-audit/r425-unit-fixture-build-v1'
receipt=json.loads((BUILD/'result.json').read_text())
assert receipt['exit_status']==0, 'fixture build did not succeed'
exe=ROOT/'src/_build/default/UnitConstantFixture.exe'
assert exe.is_file(), 'expected fixture executable absent'
sha=hashlib.sha256(exe.read_bytes()).hexdigest()
output=BUILD/'postbuild-executable-receipt.json'
assert not output.exists(), 'refuse to overwrite prior postbuild receipt'
data={'status':'read-only postbuild artifact checksum','build_result_sha256':hashlib.sha256((BUILD/'result.json').read_bytes()).hexdigest(),'executable_path':str(exe),'executable_sha256':sha,'executable_size_bytes':exe.stat().st_size,'no_execution_performed':True,'axioms':'NA: artifact census only'}
output.write_text(json.dumps(data,indent=2)+'\n')
print(json.dumps(data,indent=2))
