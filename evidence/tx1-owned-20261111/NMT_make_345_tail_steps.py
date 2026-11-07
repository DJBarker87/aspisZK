from pathlib import Path
E=Path(__file__).resolve().parent
P='core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8) s.proofData { «end» := s.proofStart }'
R='core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8) s.proofData {start := s.proofStart, «end» := s.proofEnd}'
items=[
 ('LengthGuard','Bounds','raw11','TailPrefixRead','if Slice.len s.proofData != s.proofEnd then .ok (.Err .InvalidAccountData) else tailPrefixRead c s'),
 ('PrefixRead','Bounds','tailPrefixRead','TailPrefixCompare',f'(do let prefix ← {P}; tailPrefixCompare c ⟨s,prefix⟩)'),
 ('PrefixCompare','HasPrefix','tailPrefixCompare','TailPrefixReply','(do let mismatch ← c.c0 core.cmp.PartialEqU8 s.proofPrefix s.candidate; tailPrefixReply c ⟨s,mismatch⟩)'),
 ('PrefixGuard','PrefixReply','tailPrefixReply','TailTagOffset','if s.prefixMismatch then .ok (.Err .InvalidAccountData) else tailTagOffset c s'),
 ('TagOffset','PrefixReply','tailTagOffset','TailTagRead','(do let offset ← lift (Usize.wrapping_add s.proofStart 8#usize); tailTagRead c ⟨s,offset⟩)'),
 ('TagRead','TagOffset','tailTagRead','TailTagExpected','(do let tag ← Slice.index_usize s.proofData s.tagOffset; tailTagExpected c ⟨s,tag⟩)'),
 ('TagExpected','TagByte','tailTagExpected','TailTagReply','(do let tag ← c.c3 NMT_stage1_owned.aspis_r1_cost_probe.transport.Variant.S2; tailTagReply c ⟨s,tag⟩)'),
 ('TagGuard','TagExpected','tailTagReply','TailSemanticRead','if s.tagByte != s.expectedTag then .ok (.Err .InvalidAccountData) else tailSemanticRead c s'),
 ('SemanticRead','TagExpected','tailSemanticRead','TailProofRange','(do let pub ← c.c5 s.statement; tailProofRange c ⟨s,pub⟩)'),
 ('ProofRange','HasPublic','tailProofRange','TailSplitByte',f'(do let proof ← {R}; tailSplitByte c ⟨s,proof⟩)'),
 ('SplitByte','HasProofSlice','tailSplitByte','TailSplitCast','(do let kbyte ← Slice.index_usize s.data 1#usize; tailSplitCast c ⟨s,kbyte⟩)'),
 ('SplitCast','HasSplitByte','tailSplitCast','TailChild','(do let k ← lift (UScalar.cast .Usize s.splitByte); tailChild c ⟨s,k⟩)')]
module={'raw11':'NMT_345Raw_11'}
for p in E.glob('NMT_345Tail*.lean'):
 import re
 for f in re.findall(r'^def (tail\w+) ',p.read_text(),re.M):module[f]=p.stem
for label,phase,before,after,rhs in items:
 deps=[module[before],'NMT_345'+after]
 (E/('NMT_345Step'+label+'.lean')).write_text(''.join('import '+m+'\n'for m in deps)+'''set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result
'''+f'''/-- Exact one-guard/call source step, same full parent and named suffix. -/
theorem step{label} {{W : Type}} (c : Calls) (s : {phase} W) :
 {before} c s = {rhs} := rfl
#print axioms step{label}
end NMT_345
''')
