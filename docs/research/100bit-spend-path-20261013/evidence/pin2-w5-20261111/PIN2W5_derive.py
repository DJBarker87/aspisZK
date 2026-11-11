"""Derive the fixture's verifier intermediate values from a pin2-w5-dump file.
Every value here is read from the native run (trace::value or a recorded
SHA-256 call); nothing is recomputed from a model.
usage: python3 -I PIN2W5_derive.py <dump.txt> <out.json>"""
import json, sys, hashlib
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
from PIN2W5_dump import Dump
DOMAIN_LENS = None
def derive(path):
    d = Dump(path); h = d.h['tx1']
    # Semantic transcript (r1_wire): seed = H(DOMAIN,[0],le32 len,public,c1);
    # per row: absorbed = H(state,[0,0xa0+row],framed), read = H(absorbed,[1]),
    # after = H(absorbed,[2]).
    i0 = next(i for i, (l, _, _) in enumerate(h) if len(l) == 5)
    seed_lens, seed_in, seed = h[i0]
    rows = []; state = seed; i = i0 + 1
    while True:
        l, inp, out = h[i]
        if not (len(l) == 3 and l[:2] == [32, 2] and inp[:32] == state and inp[32] == 0 and inp[33] >= 0xa0): break
        row = inp[33] - 0xa0
        lr, ir, read = h[i + 1]; la, ia, after = h[i + 2]
        assert ir == out + b'\x01' and ia == out + b'\x02'
        rows.append(dict(row=row, frame=list(inp[34:]), before=list(state), absorbed=list(out), read=list(read), after=list(after)))
        state = after; i += 3
    # Opening transcript (transcript.rs Transcript): starts H(domain,[tag],semantic_state)
    j = next(k for k, (l, inp, _) in enumerate(h) if k >= i and len(l) == 3 and l[1] == 1 and l[2] == 32 and inp[-32:] == state)
    ol, oin, ostate = h[j]
    op = dict(domain=oin[:ol[0]].decode(), variant=oin[ol[0]], semantic_state=list(state), state0=list(ostate), steps=[])
    st = ostate; k = j + 1
    while k < len(h):
        l, inp, out = h[k]
        seen = [bytes(x['after']) for x in op['steps'] if x['kind'] == 'block']
        if len(l) == 4 and l[0] == 32 and l[1] == 2 and (inp[:32] == st or inp[:32] in seen):
            row = inp[33] - 0xa0
            # after the query squeeze, queries_from_pairs returns one of the
            # advance states; record which one the next absorb starts from
            resumed = None if inp[:32] == st else seen.index(inp[:32])
            op['steps'].append(dict(kind='absorb', row=row, payload_len=l[3], payload_sha256=hashlib.sha256(inp[38:]).hexdigest(), before=list(inp[:32]), after=list(out), resumed_from_block=resumed))
            st = out; k += 1; continue
        if l == [32, 1] and inp[:32] == st:
            l2, i2, o2 = h[k + 1]; assert i2 == st + b'\x02'
            op['steps'].append(dict(kind='block', before=list(st), block=list(out), after=list(o2))); st = o2; k += 2; continue
        break
    op['final_state'] = list(st)
    out = dict(seed_input_lengths=seed_lens, seed_input_sha256=hashlib.sha256(seed_in).hexdigest(), seed=list(seed), seed_hex=seed.hex(),
               semantic_rows=rows, opening_transcript=op, results=d.r)
    for stage in ('tx1', 'tx2'):
        tags = sorted({t for t, _, _ in d.v[stage]})
        out[stage] = {str(t): {str(i): x for i, x in sorted(d.tag(stage, t).items())} for t in tags}
    return out
if __name__ == '__main__':
    o = derive(sys.argv[1]); Path(sys.argv[2]).write_text(json.dumps(o, indent=1) + '\n')
    print('semantic rows', len(o['semantic_rows']), 'opening steps', len(o['opening_transcript']['steps']), 'seed', o['seed_hex'])
