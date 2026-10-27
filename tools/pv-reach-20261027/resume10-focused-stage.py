"""Wait for the authorized dependency stage, then compile smallest candidates."""
import pathlib,time,json,subprocess,sys
R=pathlib.Path(__file__).resolve().parents[2];E=R/'evidence/pv-reach-20261027/resume10'
while not (E/'receipt-40405.json').exists():time.sleep(5)
assert all(json.load(open(E/f'receipt-{a}.json'))['accepted'] for a in range(40400,40406))
names=['PV_RE_BindTransport10','PV_RE_AfterChecks10']
names += [f'PV_RE_StorePrefix10{i:02d}' for i in range(12)]
names += [f'PV_RE_AfterPrefix10{i:02d}' for i in range(8)]
names += ['PV_RE_MaterialCells10']
names += [f'PV_RE_LayoutPrefix10{i:02d}' for i in range(8)]
names += ['PV_RE_NativeAssociations10','PV_Src_RecordRootDictionary','PV_Src_RecordRootReturned','PV_Src_PublicRootAssociation','PV_RE_NativePublic10']
subprocess.run([sys.executable,str(R/'tools/pv-reach-20261027/resume10-proof-queue.py'),'40406','40496']+names,check=True)
