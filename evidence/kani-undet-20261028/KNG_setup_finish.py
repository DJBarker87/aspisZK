from KNG_control import *
# Fix own pre-launch payload/attribute inputs; never change shared launcher.
r=py(f'''from pathlib import Path
import re
s=Path({B!r})/'KNG_src'
for p in [s/'crates/aspis-statement/src/pool_v1/pair_terminal.rs',s/'crates/aspis-statement/src/pool_v1/pair_tree_profile.rs',s/'crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs',s/'crates/aspis-r1-cost-probe/src/lib.rs']:
 text=p.read_text();text=re.sub(r'(#\[cfg\(kani\)\]\\n)(mod (KNG_\\w+);)',lambda m:m[1]+'#[path="'+m[3]+'.rs"]\\n'+m[2],text);p.write_text(text)
p=s/'Cargo.toml';text=p.read_text();(s/'KNG_frozen_Cargo.toml').write_text(text)
a=text.index('members = [');z=text.index('\\n]',a)+2
text=text[:a]+'members = ["crates/aspis-core","crates/aspis-statement","crates/aspis-r1-cost-probe","docs/research/v8-r0-zk-20261009/refine/writers","docs/research/v8-r0-zk-20261009/refine/blockwriters","docs/research/v8-r0-zk-20261009/refine/poseidon"]'+text[z:]
text=text.replace('exclude = ["docs"]','exclude = ["docs","crates/aspis-prover","programs","audit","xtask"]');p.write_text(text)
''');assert r.returncode==0,r.stdout+r.stderr
text=(E/'KNG_preflight.py').read_text();r=py(f'from pathlib import Path;Path({B+"/KNG_preflight.py"!r}).write_text({text!r})');assert r.returncode==0,r.stderr
sources=['KNG_preflight.py','KNG_src/Cargo.lock','KNG_src/Cargo.toml']
rc=launch('KNG_I001','metadata',['python3','KNG_preflight.py','KNG_I001'],sources)
print(rc['exit_status'])
