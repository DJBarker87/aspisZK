from pathlib import Path
import re
p=Path(__file__).resolve().parent
clean=lambda t:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',t,flags=re.M)
raw=clean((p/'extraction/generated-Funs.lean').read_text()).replace('import AspisR1Stage2AdoptedReader.FunsExternal\n','')
body=(p/'sources/Stage2ReaderExplicitDecoders.lean').read_text()
a=body.index('structure ReaderDecoders where');z=body.index('/-- [aspis_r1_stage2_adopted_resume::verifier::')
helper=body[a:z];body=body[:a]+body[z:]
old=(p/'extraction/retained-Option-ok_or.lean.txt').read_text();assert old.split()==helper[helper.index('def core.option.Option.ok_or'):].split()
for name in ['verifier.Reader.raw','verifier.Reader.e','verifier.Reader.k','verifier.reader_e_entry','verifier.reader_k_entry']:raw=raw.replace('def '+name+'\n','def '+name+'\n  (decoders : ReaderDecoders)\n')
raw=raw.replace('aspis_core.field.WideExact.from_le_bytes s','decoders.wide s').replace('aspis_core.field.QM31.from_le_bytes s','decoders.qm s').replace('core.result.Result.unwrap core.fmt.DebugTryFromSliceError r','decoders.unwrapArray r').replace('← verifier.Reader.raw 32#usize','← verifier.Reader.raw decoders 32#usize').replace('← verifier.Reader.raw 16#usize','← verifier.Reader.raw decoders 16#usize').replace('← verifier.Reader.e {','← verifier.Reader.e decoders {').replace('← verifier.Reader.k {','← verifier.Reader.k decoders {')
assert raw.split()==body.split(),'Changes beyond explicit boundary adapter'
assert clean((p/'extraction/generated-Types.lean').read_text())==(p/'sources/AspisR1Stage2AdoptedReader/Types.lean').read_text()
print('Checked unchanged generated bodies under explicit boundaries and exact retained Option.ok_or reuse')
