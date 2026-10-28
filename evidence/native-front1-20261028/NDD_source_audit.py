"""Read-only source/cache audit; no prover or build launch."""
from pathlib import Path
import json,hashlib,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',F,'crates','programs']).decode().splitlines()+['Cargo.lock']
expected={p:hashlib.sha256(subprocess.check_output(['git','show',F+':'+p])).hexdigest() for p in paths}
owned=['crates/aspis-core/src/lib.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/field/wide_exact.rs','crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/multiproof.rs','crates/aspis-r1-cost-probe/src/weights.rs']
from NDD_sources import sources
src=sources()
x=dict(expected=expected,owned=owned)
code='''from pathlib import Path
import json,hashlib
x=json.loads(PAYLOAD);b=Path('/home/dombarker/project-offloads/codex-cx-native-front1-20261028');s=b/'NDD_src';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
missing=[];exact=[];modified={};errors=[]
tails={'crates/aspis-core/src/field.rs':'\\n#[cfg(kani)]\\nmod NDD_field;\\n','crates/aspis-r1-cost-probe/src/lib.rs':'\\n#[cfg(kani)]\\nmod NDD_controls;\\n','crates/aspis-r1-cost-probe/src/multiproof.rs':'\\n#[cfg(kani)]\\n#[path="NDD_multiproof.rs"]\\nmod NDD_multiproof;\\n','crates/aspis-r1-cost-probe/src/weights.rs':'\\n#[cfg(kani)]\\n#[path="NDD_weights.rs"]\\nmod NDD_weights;\\n'}
for n,h in x['expected'].items():
 p=s/n
 if not p.is_file():missing.append(n);continue
 actual=sha(p)
 if actual==h:exact.append(n);continue
 if n not in x['owned']:errors.append(dict(path=n,expected=h,actual=actual));continue
 text=p.read_text()
 if n in tails:
  assert text.endswith(tails[n]),n
  text=text[:-len(tails[n])]
 text=''.join(line for line in text.splitlines(True) if not(line.startswith('#![cfg_attr(kani') or (('cfg_attr(kani' in line or 'cfg_attr(all(kani,NDD_bits)' in line) and 'kani::' in line)))
 if n.endswith('/field.rs'):
  for marker in ['fn qm31_from_karatsuba_channel_sums(', 'pub fn qm31_pack_base4(']:text=text.replace('    '+marker,marker)
 normalized=hashlib.sha256(text.encode()).hexdigest()
 modified[n]=dict(actual=actual,normalized=normalized,expected=h,cfg_only=normalized==h)
 if normalized!=h:errors.append(dict(path=n,reason='not exact frozen bytes after removing cfg-only instrumentation',normalized=normalized,expected=h))
allowed_missing=['crates/aspis-r1-cost-probe/src/RealR1_client.rs','crates/aspis-r1-cost-probe/src/RealR1_client_tests.rs']
assert not(set(missing)-set(allowed_missing)),missing
assert not errors,errors
setup=json.loads((b/'NDD_SETUP-reservation.json').read_text())
cache=b.parent/'codex-cx-front1-cache-20261028';unchanged=[]
# Actual imported cache pins are validated by the final pin audit as well.
print(json.dumps(dict(frozen_files=len(x['expected']),exact=len(exact),modified_cfg_only=modified,missing_disabled_clients=missing,errors=errors,own_cache=str(cache),setup_allowed=setup['allowed'])))
'''.replace('PAYLOAD',repr(json.dumps(x)))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NDD_SOURCE_AUDIT.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stderr
out=json.loads(r.stdout)
# Every captured source pinset must agree on all unchanged frozen files.
history=[]
for cfg in sorted(E.glob('NDD_K[0-9][0-9][0-9].json')):
 a=cfg.stem;p=E/a/'sources/NDD_SOURCE_PINS.json';assert p.is_file(),p
 pins=json.loads(p.read_text());err=[n for n,h in expected.items() if n not in owned and n in pins and pins[n]!=h]
 assert not err,(a,err)
 history.append(dict(attempt=a,unchanged_frozen_source_pins=True))
out['historical_pinset_checks']=history
out['harness_inputs']={n:hashlib.sha256(v.encode()).hexdigest() for n,v in src.items()}
(E/'NDD_SOURCE_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(dict(frozen_files=out['frozen_files'],exact=out['exact'],cfg_only=len(out['modified_cfg_only']),missing=len(out['missing_disabled_clients']),historical_checks=len(history))))
