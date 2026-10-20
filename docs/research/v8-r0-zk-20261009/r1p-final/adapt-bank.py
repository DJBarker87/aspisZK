#!/usr/bin/env python3
"""Replace explicitly inventoried unsupported std externals with proved models.
Requires the continuation-4 all-copy-crates extraction, never the incomplete one.
No source Rust edits; no new extraction or unsupported field is silently accepted.
"""
import pathlib, re, hashlib, json, subprocess
HERE=pathlib.Path(__file__).resolve().parent
RAW='/home/dombarker/project-offloads/codex-cx-builder-ref4-20261021/continuation4/bank-included-extraction/generated/Glue.lean'
raw=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat '+RAW],text=True)
s=raw.replace('import Aeneas\n','import R1Z.BuilderStdShift\n')
names={
 'core.array.from_fn':'R1Z.BuilderStdModels.fromFn',
 'core.iter.traits.iterator.Iterator.map.default':'R1Z.BuilderStdModels.iterMap',
 'core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next':'R1Z.BuilderStdModels.mapNext',
 'core.ops.range.Range.contains':'R1Z.BuilderStdModels.rangeContains',
 'core.ops.range.RangeInclusive.contains':'R1Z.BuilderStdModels.rangeInclusiveContains',
}
for name,model in names.items():
 pattern=r'axiom '+re.escape(name)+r'\n.*?(?=\n\n)'
 s,n=re.subn(pattern,'abbrev '+name+' := @'+model,s,count=1,flags=re.S)
 assert n==1, name
s,n=re.subn(r'axiom aspis_core.field.P : Result Std.U32','def aspis_core.field.P : Result Std.U32 := ok 2147483647#u32',s)
assert n==1
# The pinned backend Iterator record does not carry map/collect fields. These
# default-method dictionary entries are not used by the extracted caller:
# it calls standalone map.default and collect.default explicitly. Preserve next.
start=s.index('impl_def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator')
end=s.index('\n}',start)
block=s[start:end]
cut=block.index('\n  map :=')
removed=block[cut:]
s=s[:start]+block[:cut]+s[end:]
assert s.count('Std.U64.wrapping_shr p.next_pair_index n') == 1
s=s.replace('Std.U64.wrapping_shr p.next_pair_index n',
            'R1Z.BuilderStdModels.shift64 p.next_pair_index n')
assert s.count('Std.U64.wrapping_shr e 1#i32') == 1
s=s.replace('Std.U64.wrapping_shr e 1#i32', 'Std.U64.wrapping_shr e 1#u32')
assert not re.search(r'\b(axiom|sorry|admit|native_decide)\b',s)
out=HERE.parent/'lean/R1Z/BuilderBankExtracted.lean'
s += '\n#print axioms AspisBuilderGlueSource.pool_v1.pair_forest_copy_builder.merged_banks\n'
out.write_text(s)
(HERE/'bank-adaptation.json').write_text(json.dumps(dict(raw_host_path=RAW,raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),adapted_sha256=hashlib.sha256(s.encode()).hexdigest(),replacements=names,constant='aspis_core.field.P := ok 2147483647#u32',removed_unsupported_dictionary_fields=removed,shift_adapters=['U64 usize count uses proved shift64', 'literal 1i32 becomes 1u32']),indent=2)+'\n')
print(out, len(s), 'bytes')
