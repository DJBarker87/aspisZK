"""Reviewed deployed call occurrences; CLOSED labels never imply parent installation."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent;rows=[]
def add(parent,line,call,child,support,frame):
 rows.append(dict(parent='TX1:'+parent,line=line,call=call,callee=child,support=support,required_frame=frame,native_parent_installation='OPEN'))
f='prefix/root/claims/challenges/alpha immutable; transcript/hash consumption and ordered log preserved; first Err/abort stops suffix'
for line,call,child,support in [
(234,'semantic_rounds(&prefix, transcript)?','134 CLOSED','K039/040 reject,041/042 stability; AlphaDomain.source; full native success carry OPEN'),
(237,'mark(obs,2)','130 CLOSED','Observed/Finish source support; actual mark log frame OPEN'),
(238,'claims(&prefix)?','129 CLOSED','ClaimsDomain.source; SAME parser/reservation; full native call carry OPEN'),
(239,'original Challenges {lambda,chi,theta,zc,mu,eta}','parent record constructor','K010/011 field-copy window; full parent carry OPEN'),
(248,'public.terminal_qm31(&claims,&alpha,&original_challenges)','256 OPEN','No sibling result consumed; full native terminal slot OPEN'),
(249,'terminal.map_err(|_|Error::Public)?','parent Result mapping','FinishStages.afterTerminal source support; actual mapping/log OPEN'),
(250,'mark(obs,3)','130 CLOSED','Native occurrence/frame OPEN'),
(252,'core::array::from_fn(|i|claims[0][i])','parent fixed-array construction','MaskLowStep/FromFnIndices/MaskArrays.low_source; K043/044; whole native constructor transport OPEN'),
(252,'claims[0][i] for arbitrary i<16','parent bounded indexing','MaskLowStep.step; K043/044 observation, K028/029 frame'),
(253,'core::array::from_fn(|i|claims[0][16+i])','parent fixed-array construction','MaskHighStep/FromFnIndices/MaskArrays.high_source; K045/046'),
(253,'16+i and claims[0][16+i] for i<10','parent bounded indexing/add','MaskHighStep.step includes exact usize bound; K045/046 window'),
(254,'claims[0][27]','parent indexing','K047/048; MaskCanonical.domain'),
(255,'&alpha','parent argument carry','K049/050; AlphaDomain.source'),
(251,'state_only_selected_mask_value(low,high,blind,&alpha)','076 CLOSED','Arguments evaluated before call; MaskCuts.arguments/FinishMaskDomain.source; actual076 full value installation OPEN'),
(257,'prefix.validated_record(25)? [first occurrence]','141 CLOSED','FinishSlots.source; getter frame/value generated from SAME parsed prefix'),
(257,'record25.decode_k::<29>(87)?','147 CLOSED','FinishSlots.source full successful decoder/canonicality; native parent installation OPEN'),
(258,'challenges.eta.mul(terminal)','029 CLOSED','No Kani multiplication. Future emitted Lean law/domain transport OPEN'),
(258,'mask.add(eta*terminal)','024 CLOSED','Full native call/domain/frame transport OPEN'),
(258,'extra[28]','parent indexing','K024/025 source window; canonical extra via FinishSlots.source'),
(258,'previous.add(extra[28])','024 CLOSED','Full native call/domain/frame transport OPEN'),
(259,'running != masked_terminal / return Terminal','parent comparison/Result','K020/021 source helper guard only'),
(262,'mark(obs,4)','130 CLOSED','Native occurrence/frame OPEN'),
(263,'transcript.state()','146 CLOSED','State carry before first circle OPEN'),
(264,'prefix.validated_record(25)? [second occurrence]','141 CLOSED','CircleDomains.source; GetterRepeat.source models repeat; native occurrence still distinct'),
(264,'transcript.circle_validated(record25)?','142 CLOSED','CircleDomains.source at arbitrary actual transcript; native mutation/log carry OPEN'),
(265,'prefix.validated_record(26)? [first occurrence]','141 CLOSED','FinishSlots.source'),
(265,'record26.decode_k::<29>(0)?','147 CLOSED','FinishSlots.source; exact full decoder/canonicality'),
(266,'prefix.validated_record(26)? [second occurrence]','141 CLOSED','CircleDomains.source; distinct native occurrence/frame OPEN'),
(266,'transcript.circle_validated(record26)?','142 CLOSED','CircleDomains.source; second native transcript/log carry OPEN'),
(267,'mark(obs,5)','130 CLOSED','Native occurrence/frame OPEN'),
(288,'z0 == z1 / return EqualCirclePoints','parent comparison/Result','K022/023 source guard only'),
(292,'prefix.payload(2)?','139 CLOSED','Actual payload/root length/domain and Err/abort transport OPEN'),
(292,'payload2.try_into()','parent slice-array conversion','K026/027 root32 cell copy window; full native parent context OPEN'),
(292,'converted_root.unwrap()','parent unwrap/abort','Payload32 safety in actual parent still to install'),
(291,'Verified {all returned fields}','parent constructor/moves','Full roots/challenges/alpha/claims/extra/before_z1/state/z/transcript/result/log native assembly OPEN')]:add('136',line,call,child,support,f)
for line,call,child,support in [
(312,'Prefix::parse(bytes)?','138 CLOSED','K006/007 reject and008/009 stability; ObservedStages.parsed_error, ObservedTrace.parser_rejection'),
(313,'mark(obs,0)','130 CLOSED','Full native mark occurrence/log frame OPEN'),
(314,'public_transcript(public,hash,prefix.c1_root)?','131 CLOSED','ObservedContinuations.afterPublic source factor; complete native success/error carry OPEN'),
(315,'wire::begin(&prefix,&mut transcript)?','150 CLOSED','ObservedContinuations.afterBegin source factor; complete native mutation/query carry OPEN'),
(316,'mark(obs,1)','130 CLOSED','Full native mark occurrence/log frame OPEN'),
(317,'verify_finish(public,prefix,transcript,challenges,obs)','136 OPEN','SAME arguments source factor only; no child result assumed')]:add('137',line,call,child,support,'public/bytes/root immutable; owned prefix, hash and mutable transcript/challenges carried at SAME arguments; all Err/abort prefix events retained')
for line,call,child,support in [
(256,'heap::filled(LOGICAL_SEMANTIC+LOGICAL_Y1,0)','064 CLOSED','Full native allocation success/frame OPEN'),
(256,'filled.map_err(|_|Error::Allocation)?','parent Result mapping','Source buffer factor only; native exact allocation failure/abort OPEN'),
(257,'logical.split_at_mut(LOGICAL_SEMANTIC)','parent disjoint mutable split','K051/052 semantic and K053/054 values ENTRY_ONLY; disjoint post ownership/lifetime OPEN'),
(258,'proof[OFF_SEMANTIC..OFF_Y1]','parent slice bounds','K051/052 ENTRY_ONLY actual sizes/pointers'),
(258,'expand_semantic(proof_semantic,semantic)?','098 CLOSED','Full native child args/Result/owned frame OPEN'),
(259,'proof[OFF_Y1..OFF_INACTIVE]','parent slice bounds','K053/054 ENTRY_ONLY actual sizes/pointers'),
(259,'expand_values(proof_values,y1)?','099 CLOSED','Full native child args/Result/owned frame OPEN'),
(260,'logical[..LOGICAL_SEMANTIC],logical[LOGICAL_SEMANTIC..]','parent views','K055/056 semantic ENTRY_ONLY; second view/frame still OPEN'),
(260,'wide_view(proof,semantic_logical,y1_logical)?','095 CLOSED','Source factor only; complete native view/alias/lifetime/frame OPEN'),
(261,'verify_observed(public,v.semantic,hash,obs)','137 OPEN','K055/056 view ENTRY_ONLY; PrepareStages/PrepareBuffer source op9'),
(261,'verify_observed(...).map_err(|_|Error::Semantic)?','parent Result mapping','PrepareStages semantic_error/scratch source frame only'),
(262,'mark(obs,Phase::Semantic)','191 CLOSED','Actual native mark frame OPEN'),
(263,'Prepared::new(&sem,&v,hash,g)','179 CLOSED','Use actual179, not alternative new methods; full native constructor args/domain and g frame OPEN')]:add('087',line,call,child,support,'proof/public/hash immutable; allocation/logical buffer split and nonmodified partition; borrowed views live through constructor; scratch29 and observer/log full frame; first Err/abort stops suffix')
for line,call,child,support in [
(271,'k != SPLIT / return Parse','parent guard/Result','K031/032 and037/038 actual rejection/stability'),
(274,'parse_shape(proof)?','086 CLOSED','K033/034 actual Err prefix; full interpretation pending'),
(275,'canonical_scan(proof)?','084 OPEN baseline; merged NKL gated candidate','K035/036 error prefix; merged NKL_ScanRoot available, not yet installed at SAME proof'),
(276,'mark(obs,Phase::Parsed)','191 CLOSED','Full native mark/log frame OPEN'),
(277,'[E::ZERO;29]','parent fixed-array construction','K057/058 ENTRY_ONLY'),
(278,'prepare(public,proof,hash,obs,&mut g)?','087 OPEN','Full native call/post/Err/abort/log remains OPEN'),
(279,'Accumulator::new(Variant::S2)?','174 CLOSED','Exact174, not Prepared179; native state/Err carry OPEN'),
(280,'mark(obs,Phase::Prepare)','191 CLOSED','Full native mark/log frame OPEN'),
(281,'proof[OFF_FOLDED_ROOT..OFF_ROUND1]','parent slice bounds','K059/060 value and061/062 proof-cell ENTRY_ONLY'),
(281,'folded_slice.try_into()','parent32 copy','K059/060 arbitrary byte plus exact KMX configuration; parent association OPEN'),
(281,'converted_folded.unwrap()','parent unwrap/abort','Actual length/copy/abort native assembly OPEN'),
(282,'batch_merkle(proof,&p,&folded_root,0,hash)?','081 OPEN','K063/064 SAME arguments ENTRY_ONLY; no free result'),
(283,'mark(obs,Phase::Merkle(0))','191 CLOSED','Full native mark/log frame OPEN'),
(284,'QueryGeometry::for_range(&p.queries,0,k)?','181 CLOSED','K065/066 arguments ENTRY_ONLY; complete domain/Result/frame OPEN'),
(285,'BatchedWeights::new(&a.weights)?','176 CLOSED','K067/068 weights64 ENTRY_ONLY; complete result/domain OPEN'),
(286,'query_loop(proof,&p,a,&g,obs,&geometry,pending,k)?','088 CLOSED','Tx1Stages source factor; native owned state/arguments/Result/log carry OPEN'),
(287,'pending.finish(&mut a.weights)','175 CLOSED','Full native exactly-weights mutation and rest-of-a frame OPEN'),
(288,'checkpoint(&p,&a,proof,public_bytes,hash)','186 CLOSED','K069/070 arguments ENTRY_ONLY; complete bytes/hash/log/frames OPEN'),
(289,'mark(obs,Phase::CheckpointWrite)','191 CLOSED','Full native mark/log frame OPEN'),
(290,'Ok(bytes)','parent final Result','Full native bytes/owned frame/log assembly OPEN')]:add('094',line,call,child,support,'proof/public/hash and prepared immutable; g scratch, accumulator(weights/rhs/power/next), geometry and pending owned carries; every exact Err/abort/log prefix and checkpoint bytes preserved')
rows.sort(key=lambda r:(['TX1:136','TX1:137','TX1:087','TX1:094'].index(r['parent']),r['line']))
(E/'NKQ_OCCURRENCES.json').write_text(json.dumps(rows,indent=1)+'\n')
s='# NKQ source occurrence inventory\n\nTarget not yet established. Reviewed against frozen Rust4bb3b3f5. Each repeated call is separate. CLOSED identifies an available child bridge, **not** a parent installation. Every native-parent installation below remains OPEN. Component receipts are paired controls, not full native carries. Evaluation of mask arguments precedes its call despite its earlier textual line. All `?` sites require their exact Result/outer-abort transport and source prefix.\n\n'
for parent in ['TX1:136','TX1:137','TX1:087','TX1:094']:
 s+='## '+parent+'\n\n| Line | Occurrence | Child / component support | Required carry |\n|---|---|---|---|\n'
 for r in rows:
  if r['parent']==parent:s+='| '+str(r['line'])+' | `'+r['call'].replace('|','¦')+'` | '+r['callee']+'; '+r['support']+' | '+r['required_frame']+'; native-parent installation OPEN |\n'
 s+='\n'
s+='## Deployed feature exclusions\n\n136 line236 prover semantic_rounds alternative and the complete cfg(prover) block lines268–286 (all into_iter/enumerate/iter, with_alphas, WideExact::from_qm31 and trace::value occurrences) are excluded together under actual deployed features. Prover-only result fields are excluded. They are not partly credited or unfolded. There is no deployed parent loop here; emitted mask array constructors are handled by one-step bounds/frame lemmas and index-list induction. No SHA body or field multiplication is unwound.\n\nMissing full native windows are explicitly OPEN above and in NKQ_REMAINING.md; the70-run allowance ended before all could be built. The entry windows do not establish child results, lifetime/post frames or abort suffixes. Future roots must bind concrete native observations; arbitrary source dictionaries and endpoint/success equations are forbidden root premises.\n'
(E/'NKQ_OCCURRENCES.md').write_text(s)
print('Reviewed occurrences',len(rows))
