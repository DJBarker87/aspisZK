"""Source-signature audit only. Does not invoke Lean or claim native reachability."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / 'evidence/pv-top-20261029'
BASE = 'ce0015841f'
RUNJOIN = 'f3747e2d95fd6eff27fe00642fac892613cdb47d'
PREFIX = 'docs/research/v8-r0-zk-20261009/lean/'
records = []

def read(rev, path):
    data = subprocess.check_output(['git', 'show', f'{rev}:{path}'], cwd=ROOT)
    records.append(dict(revision=subprocess.check_output(
        ['git', 'rev-parse', rev], cwd=ROOT, text=True).strip(), path=path,
        git_blob=subprocess.check_output(['git', 'rev-parse', f'{rev}:{path}'],
                                        cwd=ROOT, text=True).strip(),
        sha256=hashlib.sha256(data).hexdigest(), size=len(data)))
    return data.decode()

runtime = read(BASE, PREFIX + 'R1Z/PV_RunJoin_Deployed.lean')
returned = read(RUNJOIN, PREFIX + 'R1Z/PV_RunJoin_WorldDecode33.lean')
fibres = read(RUNJOIN, PREFIX + 'R1Z/PV_RJDec_Factor.lean')
cases = read(RUNJOIN, PREFIX + 'R1Z/PV_RJDec_ResultCases.lean')
source = read(BASE, 'lean/PV_RJ4IDB_SourceTrace.lean')
native = read(BASE, 'lean/PV_RJ4IDB_NativeFactor.lean')
observation = read(BASE, 'lean/PV_RJ4IDB_Decoder.lean')
inputs = read(BASE, 'lean/PV_RJ4IDB_OpenInputs.lean')
headline = read(BASE, PREFIX + 'R1Z/PrivacyR1HeadlineDeployedReal.lean')
endpoint = read(RUNJOIN, PREFIX + 'R1Z/PV_RunJoin_Endpoint.lean')
publication = read(RUNJOIN, PREFIX + 'R1Z/PV_RunJoin_PublishSkeleton54.lean')
r24 = read(RUNJOIN, PREFIX + 'R1Z/PV_RunJoin_LinkR24Discharged54.lean')
bridge = read(RUNJOIN, PREFIX + 'R1Z/PV_RunJoin_OracleBridge38.lean')
diag = read(BASE, 'evidence/pv-diag10-20261029/PV_DIAG10_Observer.lean')
for name in ['CountSkeleton', 'OriginalCountSkeleton']:
    read(BASE, f'lean/PV_L1E_{name}.lean')

assert 'Result (Output N L C) → View K CommitHandle Aux R1Bat' in runtime
assert 'Result (Output N L C) → List (Bytes × OracleAnswer)' in runtime
assert '(r : World runtime) : Result (Output N L C)' in runtime
erasure = returned.split('def returned ', 1)[1].split('/--', 1)[0]
assert '| .ok a => .ok (a,r.world)' in erasure
assert '| .fail e => .fail e' in erasure and '| .div => .div' in erasure
assert 'calls' not in erasure
assert 'theorem no_decoder' in returned and 'theorem exists_iff' in fibres
assert 'theorem fibres_iff' in cases
assert '(r : Run W Event Aeneas.Std.Error A)' in source
assert 'r.calls.map Prod.snd' in source and 'theorem result_fibres_exact' in source
assert 'theorem native_factorization {A : Type} (t : NativeTrace A)' in native
assert 'ordered : List Event' in observation
names = re.findall(r'^def ([A-Z][A-Z0-9_]+)', inputs, re.M)
assert len(names) == 9 and len(set(names)) == 9
assert 'Fibres' not in inputs and 'returned' not in inputs
assert 'QueryScanRealLazyBound.realBad W Pr 8 h B outputs x w' in headline
assert '(realSeedQueries template outputs x rust observer_program adv w)' in headline
assert 'ProverCommitObserverQueries19.real W Pr 8' in headline
assert 'oldBad" => QueryScanRealLazyBound.realBad W Pr 8 h B outputs x' in endpoint
assert 'queries" => PrivacyR1HeadlineDeployedReal.realSeedQueries template outputs x rust observer_program' in endpoint
assert 'theorem complete : PV_RunJoin_Link_R24Sampler' in r24
assert 'theorem selected_callback' in bridge and '(op227 : ∀ claims,' in bridge
assert len(re.findall(r'^def PV_RunJoin_Link_', publication, re.M)) == 7
for channel in ['file', 'json', 'error']:
    for link in ['init', 'step']:
        assert f'theorem {channel}_{link}_link' in diag

OUT.mkdir(parents=True, exist_ok=True)
(OUT / 'source-check.json').write_text(json.dumps(dict(
    check='PASS: source signatures and erasure only', sources=records,
    nine_inputs=names, runjoin_revision=RUNJOIN,
    lean_attempts=0, native_scopes=0, kani=0, compiled_objects_reused=[],
    limitation='No elaboration, native execution, reachability proof or fibre-law discharge.'
), indent=2) + '\n')
print(f'PASS: {len(records)} pinned sources; nine inputs; Result/trace carrier mismatch recorded')
