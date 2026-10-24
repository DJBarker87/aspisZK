#!/usr/bin/env python3
"""Read-only D189 source-port, local-premise and evidence audit. No prover run."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2]; E=R/'evidence/s2w-20261023'
P=R/'docs/research/100bit-spend-path-20261013'; L=P/'lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source=R/'programs/r1-cost-probe/src/r1_pool_adapter_owned.rs'; native=source.read_text()
projection=R/'tools/s2w-20261023/S2W_wrapper/src/lib.rs'; checks=projection.read_text()
subprocess.run([sys.executable,str(R/'tools/s2w-20261023/S2W_entry_gen.py'),'--check'],check=True)
fragments={}
for n in (1,2):
 start=native.index('pub(super) fn stage'+str(n)+'(')
 a=native.index('    let owned = [',start);b=native.index('\n    ];',a)+len('\n    ];')
 fragment=native[a:b];assert checks.count(fragment)==1
 fragments[str(n)]=hashlib.sha256(fragment.encode()).hexdigest()
assert native.count('accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);')==1
assert checks.count('accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);')==1
for n in (1,2):assert native.count('stage'+str(n)+'_owned(program_id, &owned, data')==1
assert 'accounts.len() != 3' in native and 'accounts.len() != 7' in native
for a in ('kani-004','kani-019'):
 receipt=json.loads((E/a/'receipt.json').read_text());assert receipt['exit_status']==0
 for f,digest in receipt['source_hashes'].items():
  assert sha(E/a/'sources'/f)==digest,(a,f)
  if a=='kani-019':assert sha(R/'tools/s2w-20261023'/f)==digest,(a,f)
  if a=='kani-004' and f.endswith('src/lib.rs'):
   assert 'accounts[2].try_borrow_mut_data()?.copy_from_slice(&checkpoint);' in (E/a/'sources'/f).read_text()
wrappers=(L/'S2W_D189Wrappers.lean').read_text();entry=(L/'S2W_D189Entry.lean').read_text()
assert all(x in wrappers for x in ['(58295,58295)','(1880,1880)','(1768,1768)','(384,384)','(192,192)','(768,768)','(128,256)','(192,320)'])
assert 'count : Nat' in wrappers and 'allocator.allocate state size' in wrappers
assert 'allocator.cleanup allocated' in wrappers
assert 'native program e.first data' in wrappers and 'native program (e.second secondSizes) data slot' in wrappers
assert 'copy (acquire e.heap' in wrappers and 'release written (exclusiveGuard e.heap 2 0 0)' in wrappers
assert 'if bytes.val.length = len1 ∨ bytes.val.length = len2 then .Ok bytes' in entry
structures={
 'S2TrustedSdkBorrow':('S2TrustedSdkBorrow.lean','SDK fifteen primitive fields; includes cell/payload/counter and operation frames; no adapter acceptance'),
 'TrustedStd':('S2W_TrustedStd.lean','Universal single slice-copy primitive semantics; no caller postcondition'),
 'RuntimeEntrypointAdmission':('S2W_D189Consolidation.lean','Existing valid entry/alias/guard premises plus initial native SDK relatedness; no final accounts'),
 'Allocator':('S2W_D189Wrappers.lean','Runtime private allocation/cleanup region operations; no account-state capability; failures abort accepted wrapper equations'),
 'AeneasExtraction':('S2W_DigestExtraction.lean','D188 owned source and exact digest extraction; no S2 observation'),
 'P1/RuntimeSyscall':('S2W_ExtractionBoundary.lean','Hash realization and successful runtime syscall return values; no caller acceptance'),
 'CheckpointVersionBinding':('S2X_RuntimeRetention.lean','Existing protected ledger-version history, now indexed to actual post-write payload'),
 'P2Prime':('S2W_AuthenticatedInputs.lean','Existing complete-buffer runtime binding, activated by independently derived digest comparisons'),
 'CheckpointWriterConeJoin':('S2W_AuthenticatedInputs.lean','Local successful child header serialization and size'),
 'CheckpointReaderConeJoin':('S2W_AuthenticatedInputs.lean','Local successful child header digest comparisons'),
 'FirstEntryVerifierConeJoin':('S2W_ChildJoins.lean','Child accepted parser provenance on the actual proof argument'),
 'MultiproofConeJoin':('S2W_ChildJoins.lean','Child-local checked physical ranges for each batch'),
 'S8StageConeJoin':('S2W_ChildJoins.lean','Child-local checked y1 range argument'),
 'ChildConeJoin':('S2W_ExpandedChildren.lean','Typed child source execute plus value erasure; no account state input'),
 'FirstMarks/SecondMarks':('S2W_TraceSplice.lean','Child-local site layout only; actual whole outer-log segments derived'),
}
# Human-readable statement audit retained alongside exact printed declarations.
record={'status':'pass','ruling':'LOG D189, 2026-10-23 17:35; D188 extraction boundary unchanged',
 'qualification':'Source syntax/primitive contract composition audit, not a new native SDK implementation proof. Initial typed runtime interpretation, private allocator separation, TrustedStd and source/binary trust remain explicit. Historical Kani004/union019 reused within their pinned domains; no Kani replay.',
 'source_sha256':sha(source),'entry_arrays_sha256':fragments,'kani_reused':['kani-004','kani-019'],
 'native_interpretation':{'accounts':'Entry.handles / records / buffers / descriptor base and provenance; initial RuntimeEntrypointAdmission.related',
 'sdk_fields':['account_data_cell','cell_payload','cell_counter','borrow_frame','shared_ok','shared_deref','shared_drop','exclusive_ok','exclusive_deref','exclusive_drop'],
 'snapshots':'Exact source array expressions checked above; native wrapper selected-coordinate contracts + full-byte payload_bytes, to_vec_identity and borrow bracket restoration',
 'copy':'Single actual source expression checked above; TrustedStd successful copy -> returned heap -> writeBracket; no independent post-state equation',
 'allocation':'Runtime P2-P4 private allocator region plus std byte-copy/drop semantics; account projection only, no complete allocator equality claim',
 'children':'owned_account_frame induction over exact extracted signatures; accepted_owned_frame on SAME outer log in final theorem output',
 'public_route':'Authenticated writer/reader headers and complete-buffer P2Prime; FullForestAcceptedRoundtrip not needed or proved'},
 'premise_audit':{k:{'source':f,'source_sha256':sha(L/f),'review':why,'contains_S2CallerFacts_conclusion':False} for k,(f,why) in structures.items()},
 'removed_caller_hypotheses':['saveCut','tx2Cut','resumeCut','NodeRanges as caller cuts (retained only as child-local theorem ports)','firstChildY1Range as caller cut (retained only as child-local S8 port)','tx1ProofObservation','sameStoredProof','entrySize','savedAtWrite','OwnedSnapshotShape','NativeBinding','accountFrame','writtenMetadata'],
 'axioms_policy':['propext','Classical.choice','Quot.sound'],
 'release_pins_reused':json.loads((E/'source-inventory.json').read_text())['release_pins']}
output=E/'d189-source-premise-audit.json'
if '--check' in sys.argv:assert json.loads(output.read_text())==record
else:output.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'pass','premise_structures':len(structures),'same_source_arrays':len(fragments),'reused_kani_runs':2}))
