"""Read-only identity check against the adopted da36d6aa client bundle."""
from pathlib import Path
import subprocess,json,hashlib,sys
E=Path('evidence/pv-evh10-20261102')
rev='4ea2abfcc3a50f1b6e766ed41ff07cf815085a87'  # exact inspected bundle revision, never a moving branch
p='evidence/pv-c474b-20261029/client-build.json'
raw=subprocess.check_output(['git','show',rev+':'+p]);x=json.loads(raw)
assert x['sha256']=='da36d6aa36f8566ffa2ce7276546941c745bcd6325613c5a98c5517328b7def0'
assert '--cfg getrandom_backend="linux_raw"' in x['recipe']
assert '--bin devnet_spend' in x['recipe']
assert 'x86_64-unknown-linux-gnu' in x['toolchain'] and 'rustc 1.94.1' in x['toolchain']
assert x['ct_host_prover'] and not x['insecure_spend_fixture']
gp='evidence/pv-c474b-20261029/client-unit-graph.json'
graw=subprocess.check_output(['git','show',rev+':'+gp]);graph=json.loads(graw)
gunit=next(u for u in graph['units'] if u['pkg_id'].endswith('#getrandom@0.3.4') and u['target']['kind']==['lib'])
assert gunit['profile']['name']=='client' and gunit['profile']['opt_level']=='3'
assert not gunit['profile']['debug_assertions'] and not gunit['profile']['overflow_checks']
assert gunit['profile']['panic']=='abort'
src=json.load(open(E/'getrandom-034-linux-raw-source.json'))
s={r['relative']:r['text'] for r in src}
rawbody=s['src/backends/linux_raw.rs']
assert 'getrandom_syscall(dest.as_mut_ptr().cast(), dest.len(), 0)' in rawbody
assert 'dlsym' not in rawbody and 'OFFSET + 318' in rawbody
assert 'getrandom_backend = "linux_raw"' in s['src/backends.rs']
m=Path('lean/PV_EVH_LinuxRawControl.lean').read_text()
assert 'syscall (address+offset) (64-offset) buffer world' in m
assert 'else if ret = -4' in m and 'dlsym' not in m
out=dict(status='CONFIRMED: model is adopted linux_raw direct-syscall backend, not dlsym',
 evidence_class='structural source/config association, not compiler or kernel preservation',
 adopted_build_receipt=dict(revision=rev,path=p,sha256=hashlib.sha256(raw).hexdigest(),receipt=x),
 adopted_getrandom=dict(graph_path=gp,graph_sha256=hashlib.sha256(graw).hexdigest(),unit=gunit),
 dependency_source_sha256=next(r['sha256'] for r in src if r['relative']=='src/backends/linux_raw.rs'),
 source_control_sha256=hashlib.sha256(m.encode()).hexdigest(),
 correction='da36d6aa is a client binary SHA-256 prefix, not a git revision. Inherited native-sources inventory uses later user_client recipe; exact adopted devnet_spend receipt checked separately here. Backend flags match.',
 retained=['V370 source/compiled preservation','actual raw syscall ABI/kernel memory footprint','native source-frame provenance','non-MSAN artifact selection','full native entry/L3'],trust_fields_added=[],rows_removed=[])
p=E/'adopted-backend-confirmation.json'
if '--check' in sys.argv:
 old=json.load(open(p));assert old==out
else:p.write_text(json.dumps(out,indent=2)+'\n')
print(out['status'])
