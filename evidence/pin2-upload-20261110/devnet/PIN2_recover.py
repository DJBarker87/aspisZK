#!/usr/bin/env python3
"""Close leftover per-payment accounts of a failed or abandoned PIN2 payment, from the
retained seed records. Dry run by default: prints what it would close and the lamports.

usage: PIN2_recover.py PIN2_devnet.json RECEIPT_DIR [--label transfer|withdrawal ...] [--send] [--abandon]

For each label's private seed record ({key_namespace}-{label}-pin2-seeds.json under
proof_key_dir) it re-derives every possible account in a fixed order
  p0..p7 (proof attempts, upload program), s0 (statement, upload program),
  c0 (checkpoint, verifier), n0 (negative-test checkpoint, verifier)
and closes each one that is live with the expected owner: upload CLOSE [2,len,seed] or
verifier close [7,len,seed], base = payer. One transaction per account (failure path;
the normal path uses the single fixed close transaction in PIN2_spend.py).

Safety: if the receipts show TX1 landed but TX2 did not, closing the checkpoint abandons
that payment's proof; --abandon is required. Accounts with an unexpected owner, executable
flag or size are reported and never touched.
"""
import argparse, base64, json, pathlib
import PIN2_lib as L
from PIN2_seed_accounts import check_layout



def candidates(lay):
    out = [('proof', a, 'upload') for a in lay['proof_attempts']]
    out.append(('statement', lay['statement'], 'upload'))
    out.append(('checkpoint', lay['checkpoint'], 'checkpoint'))
    out.append(('negative_checkpoint', lay['negative_checkpoint'], 'checkpoint'))
    return out


def inspect(lay, fetch, upload, verifier):
    rows = []
    for role, entry, kind in candidates(lay):
        owner = upload if kind == 'upload' else verifier
        assert entry['owner'] == owner
        v = fetch(entry['address'])
        row = {'role': role, 'seed': entry['seed'], 'address': entry['address'], 'kind': kind, 'owner': owner}
        if v is None or v['lamports'] == 0:
            row['state'] = 'absent'
        elif v['owner'] != owner or v['executable'] or (kind == 'checkpoint' and len(base64.b64decode(v['data'][0])) != L.CHECKPOINT_BYTES):
            row.update(state='unexpected', live_owner=v['owner'], lamports=v['lamports'])
        else:
            row.update(state='closable', lamports=v['lamports'])
        rows.append(row)
    return rows


def main():
    a = argparse.ArgumentParser(); a.add_argument('config'); a.add_argument('receipts')
    a.add_argument('--label', action='append'); a.add_argument('--send', action='store_true'); a.add_argument('--abandon', action='store_true')
    args = a.parse_args()
    C = L.init(args.config, args.receipts); O = L.O; P = C['programs']; UP = C['upload_program']
    pkdir = pathlib.Path(C['proof_key_dir']); ns = C['key_namespace']
    report = {'send': args.send, 'labels': {}}
    for label in args.label or ['transfer', 'withdrawal']:
        path = pkdir / f'{ns}-{label}-pin2-seeds.json'
        if not path.exists():
            report['labels'][label] = {'seed_record': 'absent: nothing was allocated, nothing to close'}; continue
        tag = json.loads(path.read_text())['pin2_tag']
        lay = check_layout(L.plan('pin2_layout', pin2_tag=tag), C['payer'], UP, P['verifier'], tag)
        stage1 = (O / f'{label}-stage1.json').exists(); stage2 = (O / f'{label}-stage2.json').exists()
        rows = inspect(lay, lambda x: L.account(x)['value'], UP, P['verifier'])
        pending = stage1 and not stage2
        for r in rows:
            if r['state'] != 'closable':
                continue
            if r['role'] == 'checkpoint' and pending and not args.abandon:
                r['state'] = 'held: TX1 landed without TX2; pass --abandon to close'; continue
            if args.send:
                ix = L.plan('pin2_close_one', kind=r['kind'], owner=r['owner'], seed=r['seed'])
                res = L.send(f'recover-{label}-{r["seed"][:2]}', [ix])
                t = json.loads((O / f'recover-{label}-{r["seed"][:2]}-transaction.json').read_text())
                r.update(state='closed', signature=res['signature'], fee=t['meta']['fee'],
                         recovered=t['meta']['postBalances'][0] - t['meta']['preBalances'][0] + t['meta']['fee'])
                assert r['recovered'] == r['lamports'], 'recovery did not return exactly the rent'
        report['labels'][label] = {'stage1_landed': stage1, 'stage2_landed': stage2, 'accounts': rows,
                                   'closable_lamports': sum(r.get('lamports', 0) for r in rows if r['state'] in ('closable', 'closed')),
                                   'recovered_lamports': sum(r.get('recovered', 0) for r in rows)}
    L.write('recover-report' + ('' if args.send else '-dry-run'), report)
    print(json.dumps(report, indent=1))


if __name__ == '__main__':
    main()
