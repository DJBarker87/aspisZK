#!/usr/bin/env python3
"""Public inventory of configured retained roots; read-only, no cleanup."""
import json
from pathlib import Path
import subprocess
import sys
from r1_devnet_rpc import rpc
from Client64_inventory import build_report


def main(argv=None, public=None, rpc_call=None):
    argv = sys.argv[1:] if argv is None else argv
    config = json.loads(Path(argv[0]).read_text())
    out = Path(argv[1])
    cli = Path.home()/'.local/share/solana/install/active_release/bin/solana-keygen'
    def key_public(path):
        return subprocess.check_output([str(cli),'pubkey',str(path)], text=True,
                                       stderr=subprocess.DEVNULL).strip()
    try:
        report = build_report(config, public or key_public, rpc_call or rpc)
    except Exception:
        # Do not print exception payloads: RPC/keytool/JSON could contain secrets.
        report = dict(complete=False, errors=[{'error':'inventory validation or RPC failed'}])
    with out.open('x') as stream:
        json.dump(report, stream, indent=2); stream.write('\n')
    print(json.dumps({'complete':report['complete'], 'keys_retained':len(report.get('keys', [])),
                      'errors':report.get('errors', [])}))
    return 0 if report['complete'] else 1


if __name__ == '__main__':
    sys.exit(main())
