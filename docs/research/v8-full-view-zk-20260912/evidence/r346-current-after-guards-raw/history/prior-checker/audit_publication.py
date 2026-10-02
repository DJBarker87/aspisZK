#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,subprocess
WT=Path.cwd(); SCR=WT/'.r21-scratch/r346-after-guards-raw'; EV=WT/'docs/research/v8-full-view-zk-20260912/evidence/r346-current-after-guards-raw'
sha=lambda b:hashlib.sha256(b).hexdigest()
def H(p):return sha(Path(p).read_bytes())
receipt=json.loads((EV/'aspis-focus-1790938589371152000.receipt.json').read_text())
audit=json.loads((SCR/'raw-binding-audit.json').read_text())
source=EV/'source/AspisR346AfterGuardsRaw.lean'; saved=EV/'AspisR346AfterGuardsRaw.compile-snapshot.lean'; current=WT/'docs/research/v8-full-view-zk-20260912/lean/AspisR346AfterGuardsRaw.lean'
assert H(source)==H(saved)==H(current)==receipt['source_sha256']=='8035e6ba3d723e709c8897e65bc8517a849207857f03fe6979612f8e0d5b83e8'
assert receipt['source_revision']=='56a931fc3879354a2fa584e73bd0a1d412714851'
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(); assert rev==receipt['source_revision']
subprocess.run(['git','cat-file','-e',receipt['source_revision']+'^{commit}'],check=True)
# Exact frozen selected-fragment extraction and local copied Error declaration.
s=(SCR/'provenance/R292Funs.input.lean').read_text(); begin='        let i1 := Slice.len xs\n'; end='        ok (core.result.Result.Ok (ox2, oy2))\n'; i=s.index(begin); j=s.index(end,i)+len(end); frag=s[i:j]
assert sha(frag.encode())==audit['fragment_sha256']
assert (SCR/'selected-source-fragment.txt').read_text().endswith(frag)
types=(SCR/'provenance/R292Types.input.lean').read_text(); e0=types.index('/-- [aspis_v8_performance_host::Error]'); e1=types.index('/-- [aspis_v8_performance_host::circle_norm::joined_inverse::line_norm::r110_norm::batch::closure]',e0); err=types[e0:e1]
lean=(SCR/'AspisR346AfterGuardsRaw.lean').read_text(); assert err in lean and sha(err.encode())==audit['error_declaration_sha256']
assert 'import AspisR316SliceLastRaw' in lean and 'open AspisR316SliceLastRaw' in lean
assert 'import AspisR156FullFreeze.Types' not in lean
assert 'AspisR346AfterGuardsRaw.Error' in lean
# Direct import hashes match both receipt and current pinned source files.
import_hashes=receipt['direct_local_import_sha256']; names={'AspisR318BatchPrefixRaw':'AspisR318BatchPrefixRaw.lean','AspisR305BatchReverseRaw':'AspisR305BatchReverseRaw.lean','AspisR278PrivateInverseRaw':'AspisR278PrivateInverseRaw.lean','AspisR340BatchOutputRaw':'AspisR340BatchOutputRaw.lean','AspisR316SliceLastRaw':'AspisR316SliceLastRaw.lean'}
for mod,fn in names.items(): assert H(WT/'docs/research/v8-full-view-zk-20260912/lean'/fn)==import_hashes[mod],mod
log=(EV/'logs/aspis-focus-1790938589371152000.log').read_bytes(); assert sha(log)==json.loads((EV/'SHA256SUMS.json').read_text())['logs/aspis-focus-1790938589371152000.log']
logtxt=log.decode(); assert 'Exit status: 0' in logtxt and 'Swaps: 0' in logtxt
axioms=(EV/'axioms.txt').read_text(); assert all(a in axioms for a in receipt['complete_print_axioms']); assert 'sorryAx' not in axioms and 'native_decide' not in axioms
# Exact staging-bundle byte copy, checked against its staging manifest.
bundle=EV/'staging-bundle'
for line in (bundle/'SHA256SUMS').read_text().splitlines():
 h,rel=line.split('  ',1); assert H(bundle/rel)==h,rel
# Byte-preservation records, intentionally hashing full source and log bytes.
formatting={'source_snapshot_sha256':H(saved),'promoted_source_sha256':H(current),'compile_log_sha256':sha(log),'source_bytes_identical':True,'compile_log_newline_bytes_preserved':True,'source_newline_bytes_preserved':True}
(EV/'formatting-preservation.json').write_text(json.dumps(formatting,indent=2)+'\n')
report={'status':'verified saved publication evidence; no Lean rerun','target':receipt['target'],'compile_source_sha256':H(saved),'promoted_current_target_sha256':H(current),'compile_revision':receipt['source_revision'],'current_revision':rev,'ancestor_commit_present':True,'source_fragment_lines':[527,605],'source_fragment_sha256':sha(frag.encode()),'error_copy_sha256':sha(err.encode()),'R316_definition_sha256':audit['R316_Slice_last_binding']['target_sha256'],'R316_binding_explicit_in_target':True,'direct_import_hashes_verified':sorted(import_hashes),'exit_status':receipt['exit_status'],'wall_time':receipt['wall_time'],'peak_rss_kib':receipt['peak_rss_kib'],'swaps':receipt['swaps'],'resource_caps':receipt['resources'],'complete_axioms':receipt['complete_print_axioms'],'all_staging_bundle_hashes_verified':True,'scope_limit':'Raw fragment compiles; no execution correspondence, guard proof, or source library semantic claim.'}
(WT/'.r21-scratch/r346-publication-audit/audit.json').write_text(json.dumps(report,indent=2)+'\n')
shutil=None
print(json.dumps(report,indent=2))
