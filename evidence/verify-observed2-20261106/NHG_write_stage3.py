from pathlib import Path
import json,lzma,hashlib,subprocess,importlib.util,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
old=json.loads(subprocess.check_output(['git','show','6ff7634f515:'+str((E/'NHG_CLOSED.json').relative_to(R))]))
ledger=json.loads(lzma.decompress((R/'evidence/ledger9-20261105/NGZ_LEDGER.json.xz').read_bytes()));names={r['row']:r['function']for r in ledger['rows']}
trust='P6/D188 option-A native semantic transport RECLASSIFICATION; retained ABI/compiler/library/Aeneas/source-to-ELF and Std allocation/capacity/ownership/cleanup interpretation. Digest value remains accepted P1/RuntimeSyscall. No trust removal or new runtime assumption.'
capacity='No caller capacity1884 assumption. Native fixed-capacity windows are local storage witnesses; K007/K019 and NHG_AppendFrame lift all initialized prefix/suffix values through general allocation sizes. Pinned Std reserve/allocation/capacity/ownership/cleanup interpretation is retained. Allocation abort is the accepted partial terminal. Read-only borrows retain their actual owner/lifetime.'
def cert(row,root,edges,positives,controls,domain,domains,carriers,effects,form):
 return dict(function=names[row],rows=[row],status='CLOSED',form=form,domain=domain,native_positive=[f'NHG_K{x:03}'for x in positives],matched_control=[f'NHG_K{x:03}'for x in controls],lean_root=root,domain_roots=domains,carrier_roots=carriers,ordered_effect_roots=effects,internal_edges=edges,inner_hypotheses_remaining=[],KMX_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',trust=trust,capacity_qualification=capacity,source_transport='ruling (y)/(ai); emitted full Result/effect equality plus named native cuts; no whole timed-out shape credited',modifies='Only the same output Vec or SemanticTranscript state/cursor, as applicable; all input borrows immutable. Chronological digest effects exactly the accepted packet laws. Exact rejection and cleanup under retained Std interpretation.')
new=[cert('TX1:253','AspisR1.NHG_FrontierPackets.closed_packets',['TX1:252'],[27],[28],
 'Any valid owned Vec with 1<=len<=1240 and live immutable raw frontier20x8. One native row/counter boundary with arbitrary initialized prefix/suffix; child fields domain derived at every step. No canonicality or whole-serializer-success premise.',
 ['AspisR1.NHG_FrontierFrame.stage_domain','AspisR1.NHG_FrontierPackets.row_widths','AspisR1.NHG_ProducerWidths.frontier_domain'],
 ['AspisR1.NHG_FrontierFrame.frontier_envelope','AspisR1.NHG_FieldBounds.source'],['AspisR1.NHG_FrontierFrame.source'],
 'ruling (y)/(ai); one native stage, 20-stage bounded full-Result frame composition'),
 cert('TX1:254','AspisR1.NHG_ProducerPackets.source',['TX1:252','TX1:253','TX1:255'],[32,34,36,38,40,42,45],[33,35,37,39,41,43,46],
 'Every valid immutable Public Transfer or Withdrawal and SAME full transition, all raw words arbitrary. Exact declared byte order and every first-bad Public rejection. Parent input/flag routing, one arbitrary tail boundary and owned Vec return; Std operation windows and copied snapshot coordinates compose. No chosen successful serializer or extra capacity premise.',
 ['AspisR1.NHG_ProgramChain.reached_field','AspisR1.NHG_ProgramChain.reached_frontier','AspisR1.NHG_ProducerWidths.field_domain','AspisR1.NHG_ProducerWidths.frontier_domain'],
 ['AspisR1.NHG_SnapshotViews.actual','AspisR1.NHG_SnapshotViews.carrier','AspisR1.NHG_SnapshotViews.frontier_ext','AspisR1.NHG_Lengths.returned','AspisR1.NHG_AppendFrame.grow_append'],
 ['AspisR1.NHG_ProducerPackets.emitted','AspisR1.NHG_ProgramChain.append'],
 'ruling (y)/(ai); source-associated prefix, copy window, Std operations, tail stage and full emitted packet program'),
 cert('TX1:131','AspisR1.NHG_PublicTranscript.source',['TX1:143','TX1:254'],[47],[48],
 'Every valid same Public/hash/root input. SAME actual owned producer Vec is borrowed by new, length<=1455 derived from this producer; all exact statement errors map to WireError::Public and constructor WireErrors pass unchanged. Hash/digest realization remains P1/RuntimeSyscall.',
 ['AspisR1.NHG_Lengths.returned','AspisR1.NHG_Lengths.digest_domain'],
 ['AspisR1.NHG_PublicCarrier.same_execution','AspisR1.NHG_PublicCarrier.new_carrier'],['AspisR1.NHG_PublicTranscript.code'],
 'ruling (y)/(ai); exact typed two-callee Result, owned temporary Vec borrow and digest packet composition'),
 cert('TX1:150','AspisR1.NHG_BeginFrame.composed',['TX1:141','TX1:145'],[15],[21],
 'Live Prefix from CLOSED parse138 on input length<=57607: SAME root and exact borrowed row windows, widths5..3717. SAME incoming transcript supplied by CLOSED public_transcript131 (or arbitrary valid state/cursor within the direct native window). Fixed rows0..14 establish every semantic_validated domain. Full child errors/post-states and chronological effects preserved.',
 ['AspisR1.NGX_BeginDomains.frame_domain','AspisR1.NGX_BeginDomains.cursor_step','AspisR1.NGX_PrefixCarrier.producer_domain'],
 ['AspisR1.NHG_PublicCarrier.begin_carrier','AspisR1.NHG_FrontComposition.staged'],['AspisR1.NHG_BeginFrame.effects','AspisR1.NHG_FrontComposition.staged'],
 'ruling (y)/(ai); actual getter/native callee window, SAME state carrier, 15 semantic packets and Code frame chain')]
old['functions']+=new
(E/'NHG_STAGE3_CANDIDATE.json').write_text(json.dumps(old,indent=1)+'\n')
field='crates/aspis-core/src/field.rs';profile='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'
pins={p:hashlib.sha256(subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p],cwd=R)).hexdigest()for p in [field,profile]}
(E/'NHG_RESOLUTIONS.json').write_text(json.dumps(dict(field_receiver='u32',index_receiver='u64',excluded_field_methods=['TX2:016','TX2:039'],why='value is &M31, value.0 is u32; next_pair_index is u64. The emitted fields body uses core.num.U32.to_le_bytes, and Step.index uses core.num.U64.to_le_bytes. The conservative field-carrier alternatives are examined and impossible for these receiver types; no field method target is silently pruned.',frozen_source_pins=pins,native_u64='NHG_K038/NHG_K039',native_u32='retained field K003/K005 with K017/K018 and generic K007/K019',standard_library='retained Std interpretation plus native operation windows and NHG_StdBytes/NHG_AppendFrame'),indent=1)+'\n')
spec=importlib.util.spec_from_file_location('NHG_stage3_validate',E/'NHG_stage3_validate.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
result=module.validate('NHG_STAGE3_CANDIDATE.json');assert result['status']=='PASS'
(E/'NHG_CLOSED.json').write_text(json.dumps(old,indent=1)+'\n');(E/'NHG_LEDGER_DELTA.json').write_text(json.dumps(result,indent=1)+'\n');(E/'NHG_STAGE3_VALIDATION.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps({k:result[k]for k in ['status','new_rows','new_raw_roots','scan_modules','budget_used']}))
