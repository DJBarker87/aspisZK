from pathlib import Path
import hashlib, json, sys
W = Path(__file__).resolve().parent
M = json.loads((W/'manifest.json').read_text())
def sha(p): return hashlib.sha256(p if isinstance(p, bytes) else p.read_bytes()).hexdigest()
errors=[]
for ent in M['files']:
    p=W/ent['path']
    if not p.is_file(): errors.append(f"missing {ent['path']}"); continue
    if p.stat().st_size != ent['bytes']: errors.append(f"size mismatch {ent['path']}")
    if sha(p) != ent['sha256']: errors.append(f"hash mismatch {ent['path']}")
for phase in ('charon-v1','aeneas-v1'):
    r=json.loads((W/'extraction/runs'/phase/'receipt.json').read_text())
    if r.get('exit_status') != 0: errors.append(f'{phase} not green')
    if r.get('process_swaps') != 0: errors.append(f'{phase} used swap')
    if r.get('limits',{}).get('memory.swap.max') != '0': errors.append(f'{phase} swap cap not zero')
t=json.loads((W/'extraction/generated/translation.json').read_text())
if len(t.get('functions',[])) != M['extraction']['functions_count']: errors.append('function count mismatch')
by={x.get('lean_name'):x for x in t.get('functions',[])}
for name,meta in M['extraction']['nonempty_expected_declarations'].items():
    if not meta['present'] or name not in by: errors.append(f'missing expected declaration {name}')
for name in ('AspisR1WeightsPairCut.fast_pairing.EbyKDot.new','AspisR1WeightsPairCut.fast_pairing.EbyKDot.push','AspisR1WeightsPairCut.fast_pairing.EbyKDot.finish'):
    if by.get(name,{}).get('is_opaque') is not True: errors.append(f'{name} not opaque')
# Recompute the method spans from complete retained Rust files, so stale offsets fail.
def fn_span(path, sig):
    b=path.read_bytes(); start=b.index(sig.encode()); i=b.index(b'{',start); depth=0; mode='normal'; block=0; esc=False
    while i<len(b):
        c=b[i]; n=b[i+1] if i+1<len(b) else 0
        if mode=='line':
            if c==10: mode='normal'
        elif mode=='block':
            if c==47 and n==42: block+=1; i+=1
            elif c==42 and n==47:
                block-=1; i+=1
                if block==0: mode='normal'
        elif mode=='string':
            if esc: esc=False
            elif c==92: esc=True
            elif c==34: mode='normal'
        elif mode=='char':
            if esc: esc=False
            elif c==92: esc=True
            elif c==39: mode='normal'
        else:
            if c==47 and n==47: mode='line'; i+=1
            elif c==47 and n==42: mode='block'; block=1; i+=1
            elif c==34: mode='string'
            elif c==39: mode='char'
            elif c==123: depth+=1
            elif c==125:
                depth-=1
                if depth==0: return start,i+1,b[start:i+1]
        i+=1
    raise ValueError(f'unbalanced {path}:{sig}')
span=json.loads((W/'span-audit.json').read_text())
frontier=json.loads((W/'normalization-frontier.json').read_text())
if frontier.get('proved') is not False: errors.append('normalization status must remain explicitly open')
if len(frontier.get('source_order_summary',[])) < 6: errors.append('normalization order inventory incomplete')
for key,pathkey,sig in [('frozen_pair','frozen_source','    pub fn pair('),('candidate_pair','candidate_translation_input','    pub fn pair('),('free_root_shim','candidate_translation_input',' pub fn pair_root(')]:
    info=span[key]; path=W/span['retained_full_files'][pathkey]['path']; a,z,b=fn_span(path,sig)
    if (a,z,sha(b))!=(info['start_byte'],info['end_byte_exclusive'],info['sha256']): errors.append(f'balanced span mismatch {key}')
if sha(W/'candidate/input/frozen-weights-b2727acd3.rs') != M['frozen_baseline_source_sha256']: errors.append('baseline source hash mismatch')
if sha(W/'candidate/input/source.rs') != M['basis_source_sha256']: errors.append('candidate basis source hash mismatch')
for p in W.rglob('*'):
    if p.is_file() and p.suffix in {'.olean','.ilean','.ir','.exe','.o','.a'}: errors.append(f'forbidden binary/object {p.relative_to(W)}')
if errors:
    print('\n'.join(errors)); sys.exit(1)
print(f"PASS {M['schema']}: {len(M['files'])} pinned files; {len(by)} translated functions; extraction receipts green; balanced source spans recomputed; EbyK stubs flagged nonsemantic")
