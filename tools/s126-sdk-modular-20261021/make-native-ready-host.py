#!/usr/bin/env python3
"""Ready runner: std-any is replaced in typed Rust, comparison in audited C."""
from pathlib import Path
R=Path(__file__).resolve().parents[2];s=(R/'tools/s126-sdk-modular-20261021/run-sdk-shared-prefix-host.py').read_text()
a=s.index("scans=[");b=s.index("entries=[",a)
s=s[:a]+"scan='__s126_scan_already_replaced_in_typed_rust';pretty='checked_native_scan';"+s[b:]
needle="if plain:cmds[-1].remove('--json-ui')";assert s.count(needle)==1
s=s.replace(needle,"cmds=[c for c in cmds if not (scan in c and ('--remove-function-body' in c or '--generate-function-body' in c))]\ncmds=[[str(O/'comparison-linked.out') if a==str(O/'abstract.out') else a for a in c] for c in cmds]\n"+needle)
needle=" raise SystemExit(subprocess.call(['systemd-run'";a=s.index(needle)
s=s[:a]+" p=H/(tag+'-input.json');m=json.loads(p.read_text());m['source_scope']='native_reference_constructor_preconditions';m['qualification']='One native first-entry execution with actual SDK and typed-Rust pointwise sound scan and C comparison summaries; sampled original zero/prefix/tag image and every reference metadata precondition are assertions. No paired execution, frame assumption or full S2 claim.';p.write_text(json.dumps(m,indent=2)+'\\n')\n"+s[a:]
print(s,end='')
