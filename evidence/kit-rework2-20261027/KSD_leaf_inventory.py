"""Pin exact closed-leaf targets; never infer whole-kit domain admission."""
from pathlib import Path
import hashlib,json,re
E=Path(__file__).resolve().parent
base='evidence/'; low=base+'leaf-sampler1-20261027/LPk_LEAF.md';codec=base+'leaf-p6-10-20261027/';dec=base+'leaf-p6-12-20261027/';view=base+'leaf-p6-13-20261027/';circle=base+'leaf-p6-14-20261027/';prepared=base+'leaf-p6-18-20261027/'
rows=[
('low_base_p_digits','AspisR1Post25Sampler.sampler.low_base_p_digits','sampler.low_base_p_digits','docs/research/100bit-spend-path-20261013/lean-candidates/post25-ordinary-sample-candidate-20261020/sanitized-sources/Funs.lean',low,'Every 32-byte block; eight ordered quotient writes; full digit array and remaining quotient.','KSD_LeafLow'),
('echeck','verifier.echeck','verifier.echeck',codec+'LPl_Kit_FunsExternal.lean',codec+'LPl_echeck_LEAF.md','Every length 0..2272 and both k values; all rejection prefixes.','KSD_LeafCodec'),
('check_values','compact.check_values','compact.check_values',codec+'LPl_Kit_FunsExternal.lean',codec+'LPl_check_values_LEAF.md','Every 464-byte release input; complete first-error Result.','KSD_LeafCodec'),
('validate_record_fields','r1_wire.validate_record_fields','r1_wire.validate_record_fields',codec+'LPl_Kit_FunsExternal.lean',codec+'LPl_validate_record_fields_LEAF.md','Payload lengths 0..3712, every row byte, exact first failing index.','KSD_LeafCodec'),
('expand_values','compact.expand_values','compact.expand_values',codec+'LPl_Kit_FunsExternal.lean',dec+'LPn_expand_values_LEAF.md','Source lengths 0..1856 and destination 0..3712; malformed lengths and arbitrary bytes; complete mutable frame.','KSD_LeafCodec'),
('decode_k','r1_wire.ValidatedRecord.decode_k','r1_wire.ValidatedRecord.decode_k',dec+'LPn_Kit_DecodeModels.lean',dec+'LPn_decode_k_LEAF.md','N=1/28/29; all offsets/row bytes; framing length 5..3717; exact overflow/first error.','KSD_LeafDecode'),
('claims','r1_semantic.claims','r1_semantic.claims',dec+'LPn_Kit_DecodeModels.lean',dec+'LPn_claims_LEAF.md','Genuine Prefix and SAME 3717-byte framed row25; owned allocation partition required; raw cohort equality only after accepted-to-cohort.','KSD_LeafDecode'),
('Dot.push','fast_pairing.canonical.Dot.push','fast_pairing.canonical.Dot.push',dec+'LPn_Kit_DotModel.lean',dec+'LPn_Dot_push_LEAF.md','All U64 accumulator states and arbitrary Q input words; exact wrapping state/Result after nominal project.','KSD_LeafDecode'),
('wide_view','verifier.candidate.wide_view','verifier.candidate.wide_view',dec+'LPn_Kit_DecodeModels.lean',view+'LPo_wide_view_LEAF.md','Every adopted 57607-byte proof and arbitrary semantic/y1; broader Lean length>=10055 is not broader native credit.','KSD_LeafDecode'),
('semantic_boundary','r1_semantic.semantic_boundary','r1_semantic.semantic_boundary',dec+'LPn_Kit_DecodeModels.lean',view+'LPo_semantic_boundary_LEAF.md','SAME 28-element polynomial from adopted row15..24 decoder; canonicality derived.','KSD_LeafDecode'),
('circle_closure','AspisR1CircleSampleWrapper.sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once','sampler.circle_sample.closure.Insts.CoreOpsFunctionFnOnceTupleCirclePointErrorSecureCirclePoint.call_once',circle+'LPp_WrapperFuns.lean',circle+'LPp_circle_sample_LEAF.md','Both CircleRow constructors, arbitrary initial/post-draw capture and either error; exact row-specific native fallback with LPk sampler and R72 mapper associations.','KSD_LeafCircle'),
('checkpoint','AspisR1.CheckpointBytes5Writer.writer','writer','docs/research/100bit-spend-path-20261013/lean/CheckpointBytes5Writer.lean',base+'leaf-p6-11-20261027/LPm_checkpoint_LEAF.md','S1S7S8StateProvenance: S2,64 weights,next10,22 queries<262144,canonical fields and reached model agreement; exact attempted digest order.','KSD_LeafCheckpoint'),
('prepared_claim','AspisR1.LPq_PreparedClaim.program','program','lean/LPq_PreparedClaim.lean',prepared+'LPt_prepared_claim_LEAF.md','SAME installed semantic finish; compact464/output928 and checked expansion; canonical gamma/inactive/kappa and SAME successful powers29; complete LPt native_result statement applies.','KSD_LeafPrepared'),
]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
out=[]
for leaf,target,name,file,packet,domain,module in rows:
 p=Path(file);s=p.read_text();m=re.search(r'(?m)^def\s+'+re.escape(name)+r'(?=\s|:|\{|\()',s);assert m,(leaf,file)
 # declaration extent ends before next documentation, declaration, or namespace end
 tail=s[m.start():];stop=re.search(r'(?m)^(/--|def\s|theorem\s|end(?:\s|$))',tail[m.end()-m.start():]);end=(m.end()-m.start()+stop.start()) if stop else len(tail)
 span=tail[:end].rstrip()+'\n'
 packetp=Path(packet)
 out.append(dict(leaf=leaf,target=target,source=file,source_sha256=sha(p),declaration_line=s[:m.start()].count('\n')+1,declaration_span_sha256=hashlib.sha256(span.encode()).hexdigest(),packet=packet,packet_sha256=sha(packetp),domain=domain,selector_module=module,whole_kit_use='OPEN: no KIT2 caller-domain or nominal transport proof',admission='existing CLOSED P6 credit only within packet domain; selector is exact alias, not raw-carrier installation'))
(E/'KSD_leaf_targets.json').write_text(json.dumps(dict(rows=out,leaf_count=len(out),all_kit_domains_open=True,new_p6_credit=False),indent=2)+'\n')
print('Pinned',len(out),'exact leaf targets; all enclosing kit uses remain OPEN')
