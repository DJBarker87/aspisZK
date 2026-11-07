from pathlib import Path
import subprocess,difflib,hashlib
E=Path(__file__).resolve().parent
mods={'crates/aspis-statement/src/lib.rs':'PCI_statement_lib.rs.txt','crates/aspis-statement/src/spend.rs':'PCI_spend.rs.txt','crates/aspis-statement/src/pool_v1/pair_tree_profile.rs':'PCI_pair_tree_profile.rs.txt','programs/aspis-pool/src/lib.rs':'PCI_pool_lib.rs.txt','programs/aspis-pool/src/pair_forest.rs':'PCI_pair_forest.rs.txt','programs/aspis-pool/src/history.rs':'PCI_history.rs.txt','programs/aspis-pool/src/deposit_transport.rs':'PCI_deposit_transport.rs.txt'}
for root,names in [('crates/aspis-statement/src/',['PCI_NoteNative.rs','PCI_NoteReference.rs','PCI_NoteCallers.rs']),('crates/aspis-statement/src/pool_v1/',['PCI_ValidateNative.rs','PCI_ValidateReference.rs','PCI_ValidateFission.rs','PCI_ValidateWindows.rs','PCI_SingleNative.rs']),('programs/aspis-pool/src/',['PCI_CountNative.rs','PCI_RootNative.rs','PCI_DepositNative.rs','PCI_DepositReference.rs','PCI_DepositFission.rs'])]:
 for n in names:mods[root+n]=n
patch=[]
for dest,src in mods.items():
 rev='b936275465' if dest.startswith('programs/') else '4bb3b3f5'
 r=subprocess.run(['git','show',rev+':'+dest],capture_output=True,text=True)
 old=r.stdout if r.returncode==0 else '';new=(E/src).read_text()
 patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+dest if old else '/dev/null',tofile='b/'+dest))
p=E/'PCI_HARNESS.patch';p.write_text(''.join(patch))
(E/'PCI_HARNESS.patch.sha256').write_text(hashlib.sha256(p.read_bytes()).hexdigest()+'  PCI_HARNESS.patch\n')
print('PCI scratch harness patch refreshed; shipped source untouched')
