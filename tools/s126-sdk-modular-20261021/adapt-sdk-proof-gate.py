#!/usr/bin/env python3
"""Reuse literal full ProgramError and the prior concrete std Option interpreter."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021';I=Path(sys.argv[1]);O=Path(sys.argv[2]);O.mkdir(exist_ok=True,parents=True)
t=(I/'Types.lean').read_text();f=(I/'Funs.lean').read_text();external=(I/'FunsExternal_Template.lean').read_text()
def error(s):
 a=s.index('inductive solana_program_error.ProgramError where');ends=[x for x in [s.find('\n/--',a),s.find('\nend ',a),s.find('\ndef ',a)] if x!=-1];return s[a:min(ends)].strip()
prior=(D/'S2OwnedStage1TypesV1.lean').read_text();norm=lambda x:re.sub(r'\s+',' ',x).strip();assert norm(error(t))==norm(error(prior))
assert re.findall(r'^axiom ([A-Za-z0-9_.]+)',external,re.M)==['core.option.Option.ok_or']
raw=f;ns='AspisS2OwnedStage1.SdkReference.ProofGate'
f=f.replace('import AspisS2SdkProofGate.Types','import S2SdkOwnedInstallationV1').replace('import AspisS2SdkProofGate.FunsExternal\n','').replace('namespace AspisS2SdkProofGate','namespace '+ns).replace('end AspisS2SdkProofGate','end '+ns)
f=re.sub(r'^set_option (maxHeartbeats|maxRecDepth) .*\n','',f,flags=re.M)
f=f.replace('core.option.Option.ok_or','AspisS2OwnedStage1.SourceInstallation.stdOption')
f+='\n#print axioms '+ns+'.prefix_different\n#print axioms '+ns+'.reference_gate\n'
(O/'S2SdkProofGateModelV1.lean').write_text(f)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(O/'sdk-proof-gate-emission-adapter.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',raw_types_sha256=sha(t),raw_funs_sha256=sha(raw),raw_external_sha256=sha(external),source_sha256=sha(f),program_error_literal_equal=True,external_interpretation={'core.option.Option.ok_or':'AspisS2OwnedStage1.SourceInstallation.stdOption'},qualification='Isolated stage1 guard reference, full existing ProgramError reused after literal declaration check. Prior standard Option interpreter installed explicitly. Native guard equivalence, loop/guard totality and complete parent consumption are separate gates; no whole SDK/caller closure.'),indent=2)+'\n')
