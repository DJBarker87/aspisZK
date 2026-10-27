from pathlib import Path
import subprocess,hashlib,json
B=Path(__file__).resolve().parent;S=B/'XRa_toolchain/aeneas'
audit=json.loads((B/'XRa_historical_extended-tool-audit.json').read_text())
def git(*args):return subprocess.check_output(['git',*args],cwd=S,text=True).strip()
assert git('write-tree')=='5a843e70672e4139232b2fdcb52a0c1fbd4b1619'
subprocess.run(['git','apply','--check','--unidiff-zero',str(B/'XRa_aeneas.patch')],cwd=S,check=True)
subprocess.run(['git','apply','--unidiff-zero',str(B/'XRa_aeneas.patch')],cwd=S,check=True)
subprocess.run(['git','add','-f','--all'],cwd=S,check=True)
tree=git('write-tree');changed=set(git('diff','--name-only','5a843e70672e4139232b2fdcb52a0c1fbd4b1619',tree).splitlines())
rows=[]
for f,want in audit['exact_changed_files'].items():
 h=hashlib.sha256((S/f).read_bytes()).hexdigest();rows.append({'path':f,'expected':want,'actual':h,'match':want==h})
result={'base_tree':'5a843e70672e4139232b2fdcb52a0c1fbd4b1619','patched_tree':tree,'historical_recipe_claimed_patched_tree':audit['build_recipe_expected_tree'],'changed_files_exact':changed==set(audit['exact_changed_files']),'file_hashes':rows}
(B/'XRa_source_pin_contradiction.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result),flush=True)
assert result['changed_files_exact'] and all(x['match'] for x in rows),result
