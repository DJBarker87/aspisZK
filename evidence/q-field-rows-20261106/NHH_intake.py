from pathlib import Path
import subprocess,json,hashlib,difflib
E=Path(__file__).resolve().parent
paths=['evidence/slice-q-compose6-20261104/NFG_ROW_EXTRACTION_PINS.json','evidence/slice-q-compose6-20261104/NFG_row_extracted/NFG_InverseRef/Funs.lean','evidence/slice-q-compose6-20261104/NFG_row_extracted/NFG_InverseRef/Types.lean','evidence/slice-q-compose6-20261104/NFG_L035/receipt.json','evidence/slice-q-compose6-20261104/NFG_L035/sources/NFG_InverseRef/Funs.lean','evidence/slice-q-compose6-20261104/NFG_NegAssociation.lean','evidence/slice-q-compose6-20261104/NFG_QNegAssociation.lean','evidence/slice-q-compose6-20261104/NFG_L085/stdout.log']
revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();rows=[]
for p in paths:
 data=subprocess.check_output(['git','show',revision+':'+p]);h=hashlib.sha256(data).hexdigest();q=E/'NHH_inputs'/(h+'.txt');q.parent.mkdir(exist_ok=True);q.write_bytes(data);rows.append(dict(source=p,revision=revision,sha256=h,stored_once=str(q.relative_to(E))))
(E/'NHH_INTAKE.json').write_text(json.dumps(dict(files=rows,usage='Read-only committed source and extraction provenance; no unvalidated native credit imported; no extraction run charged',own_modules_prefix='NHH_',actual_native_pins='NHH_SOURCE_PINS.json, NHH_INVERSE_PINS.json, NHH_QINVERSE_PINS.json'),indent=1)+'\n')
# Every included frozen Rust/manifest is pinned by the git tree; scratch mutations
# are exactly the committed harness module/root attribute and prescribed KMX.
raw=subprocess.check_output(['git','ls-tree','-r','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'],text=True)
keep=('crates/','programs/','xtask/','audit/poseidon-pair-probe/program/','tools/r1-builder-reference/','docs/research/v8-r0-zk-20261009/refine/writers/','docs/research/v8-r0-zk-20261009/refine/blockwriters/','docs/research/v8-r0-zk-20261009/refine/poseidon/','docs/research/v8-r0-zk-20261009/refine/diffharness/tests/','docs/research/v8-r0-zk-20261009/z4/','docs/research/v8-r0-zk-20261009/c3/build/','docs/research/v8-r0-zk-20261009/c3/check/')
entries=[]
for line in raw.splitlines():
 meta,n=line.split('\t',1)
 if n in ['Cargo.toml','Cargo.lock'] or n.startswith(keep):entries.append(dict(path=n,git_blob=meta.split()[2]))
(E/'NHH_FROZEN_SCAFFOLD.json').write_text(json.dumps(dict(revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',files=entries,scratch_mutations=['cfg(kani) allocator_api attribute and NHH_fields module declaration in verifier root','new NHH_fields.rs from committed payload','exact KMX_copy_stubs.patch support files'],shipped_files_changed=False),indent=1)+'\n')
# Reviewable patch; no copy of the release tree is committed.
x=json.loads((E/'NHH_QINVERSE_INPUTS.json').read_text());old=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/lib.rs'],text=True)
n='crates/aspis-r1-cost-probe/src/lib.rs';out=''.join(difflib.unified_diff(old.splitlines(True),x[n].splitlines(True),fromfile='a/'+n,tofile='b/'+n))
n='crates/aspis-r1-cost-probe/src/NHH_fields.rs';out+=''.join(difflib.unified_diff([],x[n].splitlines(True),fromfile='/dev/null',tofile='b/'+n))
(E/'NHH_harness.patch').write_text(out)
print(json.dumps(dict(imported_files=len(rows),frozen_scaffold_files=len(entries),patch_sha256=hashlib.sha256(out.encode()).hexdigest())))
