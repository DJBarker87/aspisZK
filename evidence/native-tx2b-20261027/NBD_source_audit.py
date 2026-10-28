from pathlib import Path
import json,subprocess,hashlib,re
E=Path(__file__).resolve().parent;p=json.loads((E/'NBD_MEMBERS.json').read_text());r=p['source_revision']
rows={f['id']:f for f in p['members']}
def source(f):
 b=subprocess.check_output(['git','show',r+':'+f['file']]);assert hashlib.sha256(b).hexdigest()==f['file_sha256'];return b[f['body_start_byte']:f['body_end_byte']].decode()
a=next(f for f in rows.values() if f['file'].endswith('pair_tree_profile.rs') and f['name']=='digest_is_canonical')
b=next(f for f in rows.values() if f['file'].endswith('pair_forest_accounts.rs') and f['name']=='digest_is_canonical')
assert source(a)==source(b).replace('digest','value')
# Preserve complete ordered rejection/mutation source for every unclosed member.
with (E/'NBD_FROZEN_MEMBERS.md').open('w') as out:
 out.write('# Exact frozen member bodies (source evidence only)\n\nRevision '+r+'. Not a native/cohort proof. Signatures/line ranges and whole-file hashes are in NBD_MEMBERS.json.\n')
 for f in p['members']:out.write('\n## '+f['bridge_unit']+' '+f['id']+'\n\n```rust\n'+source(f)+'\n```\n')
q={}
for path in ['docs/research/100bit-spend-path-20261013/lean/AdapterRwModel.lean','docs/research/100bit-spend-path-20261013/lean/S2W_DigestExtraction.lean','docs/research/100bit-spend-path-20261013/lean/extracted-terminal-decoder-20261016/AspisR1TerminalDecoder/Funs.lean','evidence/replay-deployed2-20261027/RPx_Deployed.lean']:
 data=Path(path).read_bytes();q[path]={'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data)}
(E/'NBD_SOURCE_AUDIT.json').write_text(json.dumps(dict(native_scanner_body_equal_after_parameter_rename=True,canonical_sources=q,warning='NBI2 retains historical cohort file locations; use canonical module pins, not old callback numbers.'),indent=2)+'\n')
print('frozen scanner identity and source pins verified')
