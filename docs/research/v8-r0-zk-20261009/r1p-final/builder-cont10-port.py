#!/usr/bin/env python3
"""Replace only the 24 forest std externals, with an explicit adapter inventory."""
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent
import subprocess,sys
raw=subprocess.check_output(['ssh','dombarker@100.108.41.90',
  'cat /home/dombarker/project-offloads/codex-cx-builder-ref9-20261021/drop-opaque-validator/generated/Admission-renamed.lean'],text=True)
assert hashlib.sha256(raw.encode()).hexdigest() == '63c3044dbe71069d760fef6ff9006a8bd887f815b2301bae1e689fe4ece2b754'
def output(p,s):
 if '--check' in sys.argv: assert p.read_text()==s, p
 else: p.write_text(s)
std=raw[:raw.index('/-- [aspis_core::field::P]')]
std=std.replace('import Aeneas','import R1Z.BuilderForestStd\nimport Aeneas.Tactic.RustAttributes')
std=re.sub(r'set_option max(?:Heartbeats|RecDepth) \d+\n','',std)
std=std.replace('namespace AspisBuilderForestDropP6','namespace R1Z.BuilderForestStdPort')
base='R1Z.BuilderForestStd.';old='R1Z.BuilderStdModels.'
adapters={
'core.array.iter.IntoIter':base+'IntoIter',
'Array.Insts.CoreIterTraitsCollectIntoIteratorTIntoIter.into_iter':base+'intoIter',
'core.iter.adapters.flatten.Flatten':base+'Flatten',
'core.iter.traits.iterator.Iterator.sum.default':base+'sumDefault',
'core.iter.traits.iterator.Iterator.any.default':base+'iterAny',
'core.iter.traits.iterator.Iterator.flatten.default':base+'flatten',
'core.iter.traits.iterator.Iterator.map.default':old+'iterMap',
'core.array.iter.IntoIter.Insts.CoreIterTraitsIteratorIterator.next':base+'arrayNext',
'core.array.from_fn':old+'fromFn',
'core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any':'R1Z.BuilderAdmissionStd.any',
'core.array.Array.map':base+'arrayMap',
'core.iter.adapters.flatten.Flatten.Insts.CoreIterTraitsIteratorIterator.next':base+'flattenNext',
'core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next':old+'mapNext',
'U64.Insts.CoreIterTraitsAccumSumU64.sum':base+'sum64',
'core.ops.range.Range.contains':old+'rangeContains',
'core.ops.range.RangeInclusive.contains':old+'rangeInclusiveContains',
'core.option.Option.ok_or':base+'okOr',
'core.option.Option.Insts.CoreOpsTry_traitTry.branch':base+'branch',
'core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual':base+'residual',
'core.result.Result.map':base+'mapResult',
'core.result.Result.map_err':'R1Z.BuilderAdmissionStd.mapErr',
'core.slice.iter.Chunks':base+'Chunks',
'core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next':base+'chunksNext',
'core.slice.Slice.chunks':base+'chunks',
}
seen=[]
def patch(m):
 name=m.group(1);seen.append(name)
 return 'abbrev '+name+' := @'+adapters[name]+'\n\n'
std=re.sub(r'axiom\s+(\S+)[\s\S]*?(?=/--|\Z)',patch,std)
assert set(seen)==set(adapters)
# Env J has the base Iterator fields, with default adapters supplied separately.
std=re.sub(r'(\n  next :=[\s\S]*?)\n  map :=[\s\S]*?\n}',r'\1\n}',std)
std+='\nend R1Z.BuilderForestStdPort\n'
p=H.parent/'lean/R1Z/BuilderForestStdPort.lean';output(p,std)
(H/'builder-cont10-std-port.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),raw_size=len(raw.encode()),std_externals=adapters,opaque_source_externals=['poseidon2.external_linear_lazy','pool_v1.pair_forest_copy_builder.records','state_only_trace.StateOnlyTraceFoundation.Insts.CoreOpsDropDrop.drop'],std_port_sha256=hashlib.sha256(std.encode()).hexdigest(),status='std declaration port only; source externals not silently replaced'),indent=2)+'\n')
print(len(adapters),'std adapters; three separate opaque source declarations')
