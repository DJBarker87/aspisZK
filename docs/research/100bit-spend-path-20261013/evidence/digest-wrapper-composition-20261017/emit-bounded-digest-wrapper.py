from pathlib import Path
import json,hashlib
src=Path('/tmp/DigestWrapperSource.lean');s=src.read_text();old='''  let i8 ← core.num.U64.trailing_ones source.next_pair_index
  let i9 ← lift (UScalar.cast .Usize i8)
  let carry ← core.cmp.min core.cmp.OrdUsize i9 20#usize
''';new='''  let carry ← AspisBoundedControl.bounded_carry source.next_pair_index
'''
assert s.count(old)==1
s=s.replace('import TerminalDigestPublicLoopSource','import TerminalDigestPublicLoopSource\nimport BoundedControlSource').replace('Whole candidate public_digest_lanes wrapper. Only helper qualifications\nare changed, with an inverse source map in the accompanying manifest.', 'Bounded-carry implementation candidate for the public_digest_lanes wrapper.\nThis explicit model edit follows the reviewable Rust patch; correspondence to\na full re-extraction and release artifact is a separate open obligation.').replace('AspisR1DigestWrapperCandidate','AspisR1DigestWrapperBoundedCandidate').replace(old,new)
out=Path('/tmp/DigestWrapperBoundedSource.lean');out.write_text(s)
m={'input_model_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'original_source_manifest':'DigestWrapperSource.manifest.json','replaced_fragment':old,'replacement_fragment':new,'replacement_model_theorem':'AspisBoundedControl.Carry.bounded_carry_is_digestCarry','rust_patch':'bounded-terminal-control-20261017/candidate/proposed-source.patch','whole_modified_rust_reextraction_proved':False,'production_source_modified':False,'output_sha256':hashlib.sha256(out.read_bytes()).hexdigest()};Path('/tmp/DigestWrapperBoundedSource.manifest.json').write_text(json.dumps(m,indent=2)+'\n');print(m['output_sha256'])
