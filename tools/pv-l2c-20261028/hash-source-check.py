"""Generate/check the native hash comparison view at one owned external cut.
All other native function bodies remain byte-identical. No frozen source edit.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys
R=Path(__file__).resolve().parents[2]
D=R/'tools/pv-l2c-20261028/decoder-probe'
E=R/'evidence/pv-l2c-20261028/resume-d371'
def body(text,marker):
    start=text.index(marker); left=text.index('{',start); end=left+1; depth=1
    while depth:
        depth+=(text[end]=='{')-(text[end]=='}'); end+=1
    return left,end,text[left+1:end-1]
def compact(s): return re.sub(r'\s+','',s)
def sha(s): return hashlib.sha256(s.encode()).hexdigest()
native=(R/'crates/aspis-statement/src/poseidon2.rs').read_text().split('#[cfg(test)]')[0]
owned=(R/'tools/r1-builder-reference/poseidon.rs').read_text()
functions=[]
for name in ['mat4_owned','external_owned']:
    marker='pub fn '+name+'('
    start=owned.index(marker); a,b,content=body(owned,marker)
    functions.append(owned[start:b])
a,b,external=body(native,'fn external_linear_lazy(')
assert compact(external)==compact('''for chunk in state.chunks_exact_mut(4) { apply_mat4_lazy(chunk); }
let sums: [u64; 4] = core::array::from_fn(|column| (0..4).map(|row| state[row * 4 + column].0 as u64).sum());
for (index, value) in state.iter_mut().enumerate() { *value = M31::reduce_u62(value.0 as u64 + sums[index & 3]); }''')
_,_,matrix=body(native,'fn apply_mat4_lazy(')
assert compact(matrix)==compact('''let a = values[0].0 as u64; let b = values[1].0 as u64;
let c = values[2].0 as u64; let d = values[3].0 as u64;
values[0] = M31::reduce_u62(2 * a + 3 * b + c + d);
values[1] = M31::reduce_u62(a + 2 * b + 3 * c + d);
values[2] = M31::reduce_u62(a + b + 2 * c + 3 * d);
values[3] = M31::reduce_u62(3 * a + b + c + 2 * d);''')
replacement='\n    *state = external_owned(*state);\n'
generated=native[:a+1]+replacement+native[b-1:]+'\n'+'\n\n'.join(functions)+'\n'
spend=(R/'crates/aspis-statement/src/spend.rs').read_text()
constants='use aspis_core::field::M31;\n'
for name in ['DOMAIN_OWNER_KEY','DOMAIN_NULLIFIER','DOMAIN_NOTE','DOMAIN_MERKLE_NODE']:
    m=re.search(r'pub\(crate\) const '+name+r': M31 = M31\(([^)]+)\);',spend);assert m
    constants+='pub const '+name+': M31 = M31('+m[1]+');\n'
for name,expected in [('hash_reference.rs',generated),('domain_constants.rs',constants)]:
    p=D/name
    if '--check' in sys.argv: assert p.read_text()==expected,name
    else:p.write_text(expected)
sources=json.loads((R/'evidence/pv-l2c-20261028/resume-d369/focused-project-sources.json').read_text())
emitted=sources['R1Z.BuilderPoseidonExtracted']
# Owned array/index loops preserve explicit updates; these helpers have no
# mutable iterator continuation. This is per-function D188 inspection.
for name in ['mat4_owned','external_owned']:
    start=emitted.index('def poseidon2.builder_reference.'+name+'\n')
    end=emitted.find('/--',start)
    section=emitted[start:end if end>=0 else len(emitted)]
    assert 'next_back' not in section and 'index_mut' not in section
ct=(R/'crates/aspis-core/src/field/ct.rs').read_text()
_,_,reduce=body(ct,'pub fn reduce64(')
assert compact(reduce)==compact('''let x = (x & P as u64) + (x >> 31);
let x = (x & P as u64) + (x >> 31); subtract_p(x as u32)''')
_,_,subtract=body(ct,'pub fn subtract_p(')
assert compact(subtract)==compact('''let mask = 0u32.wrapping_sub((x >= P) as u32); x.wrapping_sub(P & mask)''')
out={'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
 'classification':'structural (K-1 substitute), external-layer range cut',
 'native_path':'crates/aspis-statement/src/poseidon2.rs','native_prefix_sha256':sha(native),
 'reference_path':'tools/r1-builder-reference/poseidon.rs','reference_sha256':sha(owned),
 'emission_module':'R1Z.BuilderPoseidonExtracted','emission_sha256':sha(emitted),
 'generated_sha256':sha(generated),'constant_sha256':sha(constants),
 'substitution':'only external_linear_lazy body; calls existing extracted external_owned; all other native function bodies byte-identical',
 'differences':[
  {'native':'four disjoint chunks_exact_mut(4)','owned':'while block<4 with base=4*block; four reads then four writes',
   'laws':['PV_L2C_ExternalGeometry.group_bounds','PV_L2C_ExternalGeometry.disjoint_groups']},
  {'native':'apply_mat4_lazy in-place','owned':'mat4_owned by value; identical four reduced expressions',
   'laws':['PV_L2C_ExternalGeometry.matrix_bounds','R1Z.PV_Src_ExternalMat4Copy.equals_copy']},
  {'native':'range(0..4).map(row*4+column).sum::<u64>()','owned':'state[col]+state[col+4]+state[col+8]+state[col+12]',
   'laws':['PV_L2C_ExternalGeometry.sum_four','PV_L2C_ExternalGeometry.lane_bound']},
  {'native':'index & 3, iter_mut enumerate','owned':'lane % 4, ascending while lane<16',
   'laws':['PV_L2C_ExternalGeometry.column_mask','R1Z.PV_Src_ExternalLaneModel.model']},
  {'native':'mutates [M31;16]','owned':'returns [M31;16], assigned back at the cut','law':'complete returned array copied by value; no observer at this cut'}],
 'reducer_native_sha256':sha(ct),'reducer_body_sha256':sha(reduce),
 'complete_result_laws':['PV_L2C_NativeReduce.reference','R1Z.PV_Src_ExternalModel.source','PV_L2C_HashRange.success'],
 'scope':'raw canonical result only; no source trace/timing refinement, no whole N3 or release-row closure',
 'Kani':'no credit claimed; historical copy-dependent external gates not used',
 'D188':'mat4_owned pure array literal; external_owned indexed reads/writes; inspected emission retains explicit Array.update state threading; no mutable iterator restoration in these two owned helpers'}
receipt=E/'decoder-probe2/receipt.json'
if receipt.exists():
    r=json.loads(receipt.read_text()); assert r['exit']==0
    invocation=json.loads((E/'decoder-probe2-invocation.json').read_text())
    for name in ['main.rs','hash_reference.rs','domain_constants.rs']:
        executed=subprocess.check_output(['git','show',invocation['revision']+':'+str((D/name).relative_to(R))],cwd=R)
        assert r['source_sha256'][name]==hashlib.sha256(executed).hexdigest(),name
        if name!='main.rs':assert executed==(D/name).read_bytes(),name
    log=(E/'decoder-probe2/out.log').read_text()
    assert 'same_input_native_owned_external_hash_comparisons=512' in log
    out['native_differential']={'receipt':str(receipt.relative_to(R)),
      'receipt_sha256':hashlib.sha256(receipt.read_bytes()).hexdigest(),'comparisons':512,
      'executed_source_revision':invocation['revision'],
      'classification':'finite same-input validation; actual public hash APIs versus same native hash bodies at one owned external substitution',
      'modes':['owner key','note commitment','nullifier','node compression']}
else:out['native_differential']='pending; no structural credit before collection'
(E/'hash-source-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('Checked exact native matrix/external bodies; generated one-call external substitution; retained all other hash bodies')
