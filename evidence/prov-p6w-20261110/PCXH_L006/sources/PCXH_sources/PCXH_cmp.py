# PCXH_cmp.py: fresh declaration-level comparison of NHT_Constants and CurrentCompactCallerModelV1, ledger30-chain object vs L187 object, with the L187 replay's own comparison tool (read-only).
# Runs as one step inside a capped scope (PCXH_run.py python-step mode). Prints one JSON document on stdout.
import json, hashlib, subprocess, pathlib, sys, os
W = pathlib.Path('/home/dombarker/project-offloads/codex-cx-replay-l187-20261109')
tool = W / 'tools' / 'L187_Compare'
sha = lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
chain = json.load(open('PCXH_sources/PCXH_NNN_PATHS.json'))
l187 = [str(W / 'final/objs'), str(W / 'objs'), str(W / 'base_ref')]
def find(roots, m):
    rel = m.replace('.', '/') + '.olean'
    for r in roots:
        p = pathlib.Path(r) / rel
        if p.is_file(): return str(p)
    return None
mods = ['NHT_Constants', 'CurrentCompactCallerModelV1']
out = dict(schema='PCXH_DECL_COMPARE_RAW/1', tool=str(tool), tool_sha256=sha(tool), tool_bytes=tool.stat().st_size, brief_expected_prefix='c5f43e8e', tool_matches_brief_prefix=sha(tool).startswith('c5f43e8e'), modules={})
cmp_dir = pathlib.Path('PCXH_cmp_work'); cmp_dir.mkdir(exist_ok=True)
def run(tag, rows):
    t = cmp_dir / (tag + '.tsv'); j = cmp_dir / (tag + '.jsonl')
    t.write_text(''.join('%s\t%s\t%s\n' % r for r in rows))
    r = subprocess.run(['timeout', '120', str(tool), str(t), str(j)], capture_output=True, text=True)
    res = {}
    if j.exists():
        for l in j.read_text().splitlines():
            x = json.loads(l); res[x.get('module', '?')] = x
    return dict(exit=r.returncode, stderr=r.stderr[-300:], results=res)
fw = []; rv = []; ctl = []
for m in mods:
    a = find(chain, m); b = find(l187, m)
    out['modules'][m] = dict(ledger30_chain_object=a, ledger30_sha256=sha(a) if a else None, l187_object=b, l187_sha256=sha(b) if b else None,
                             ledger30_bytes=pathlib.Path(a).stat().st_size if a else None, l187_bytes=pathlib.Path(b).stat().st_size if b else None)
    fw.append((m, a, b)); rv.append((m, b, a)); ctl.append((m, b, b))
out['forward_ledger30_to_l187'] = run('fwd', fw)
out['reverse_l187_to_ledger30'] = run('rev', rv)
out['control_l187_vs_itself'] = run('ctl', ctl)
print('PCXH_CMP_JSON ' + json.dumps(out))
sys.exit(0 if all(out[k]['exit'] == 0 for k in ('forward_ledger30_to_l187', 'reverse_l187_to_ledger30', 'control_l187_vs_itself')) else 1)
