from KNG_control import *
text=(E/'KNG_metadata.py').read_text();r=py(f'from pathlib import Path;Path({B+"/KNG_metadata.py"!r}).write_text({text!r})');assert r.returncode==0,r.stderr
for i,crate in enumerate(['aspis-r1-cost-probe','aspis-statement'],5):
 rc=launch(f'KNG_I{i:03}','metadata',['python3','KNG_metadata.py',f'KNG_I{i:03}',crate],['KNG_metadata.py','KNG_src/Cargo.lock','KNG_src/Cargo.toml']);print(crate,rc['exit_status'])
