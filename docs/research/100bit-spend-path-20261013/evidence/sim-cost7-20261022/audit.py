"""Read-only source audit. Does not compile Lean or certify execution costs."""
import hashlib,json,pathlib,subprocess,sys
repo=pathlib.Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
ev=pathlib.Path(__file__).resolve().parent
root=pathlib.Path('docs/research/v8-r0-zk-20261009')
paths=[
 'crates/aspis-r1-cost-probe/src/sim.rs',
 'crates/aspis-r1-cost-probe/src/r1_wire.rs',
 'crates/aspis-r1-cost-probe/src/transcript.rs',
 'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs',
 *[str(root/'lean'/p) for p in [
 'R0Z/ZkStatement.lean','R0Z/RefPayload.lean','R1Z/GamesR1.lean',
 'R1Z/PrivacyR1AcctModel.lean','R1Z/PhaseProtocolInstanceBin.lean',
 'R1Z/PhaseMessageEncodingBin.lean','R1Z/PhaseSamplerParserBin.lean',
 'R1Z/RomFiniteBin.lean','R1Z/PhaseWireLog2Bin.lean',
 'R1Z/BuilderPublicProjection.lean','R1Z/PredicateR1.lean',
 'R1Z/CertCheckSound.lean','R1Z/SimCostIdeal.lean',
 'R1Z/SimCostRelativeIdeal.lean','R1Z/SimCostRelativeReplay.lean',
 'R1Z/SimCostOuterRetry6.lean','R1Z/PrivacyR1HeadlineV2SimProto.lean']],
 str(root/'z4/z9e.rs')]
files=[]
for p in paths:
 b=(repo/p).read_bytes()
 files.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
endpoint=(repo/root/'lean/R1Z/PrivacyR1HeadlineV2SimProto.lean').read_text()
context,body=endpoint.split('theorem privacy_headline_v2_sim_proto',1)
signature='theorem privacy_headline_v2_sim_proto'+body.split(' := by',1)[0]+'\n'
assert '(sim_preparation : SimCostIdeal.Preparation' in signature
expected={'endpoint-context.lean.txt':context,'endpoint-before.lean.txt':signature,
          'endpoint-after.lean.txt':signature,'endpoint.diff':''}
for name,content in expected.items():
 p=ev/name
 if '--check' in sys.argv: assert p.read_text()==content, name
 else: p.write_text(content)
record=dict(kind='source inspection; no formal release result',source_revision='b641f67ac',
 files=files,endpoint_signature_sha256=hashlib.sha256(signature.encode()).hexdigest(),
 theorem_changes=[],shipped_source_changes=[],formal_builds=[],
 missing_interface='source public serialization and complete observable metadata to total R1Wire/Meta instance')
p=ev/'source-audit.json'
if '--check' in sys.argv: assert json.loads(p.read_text())==record
else:p.write_text(json.dumps(record,indent=2)+'\n')
print(f'PASS: {len(files)} pinned sources; identical endpoint signatures; no cost theorem claimed')
