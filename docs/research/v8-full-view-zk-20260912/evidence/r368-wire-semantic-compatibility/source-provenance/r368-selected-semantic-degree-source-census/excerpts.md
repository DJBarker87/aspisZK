## production_terminal_core — `crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs` (SHA256 13b68f6db428268b2504068d79c88262e36d9abd22fb60e345612eff6e2cd90b)

### Lines 101–260
```text
101: fn lift_m31(value: M31) -> QM31 {
102:     QM31::from_cm31(CM31::from_m31(value))
103: }
104: 
105: #[inline(always)]
106: fn add_preweighted<const N: usize>(
107:     packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
108:     start: usize,
109:     values: &[QM31; N],
110: ) {
111:     let first = start / 4;
112:     let last = (start + N - 1) / 4;
113:     for group in first..=last {
114:         let lanes: [QM31; 4] = core::array::from_fn(|slot| {
115:             let source = 4 * group + slot;
116:             if source >= start && source < start + N {
117:                 values[source - start]
118:             } else {
119:                 QM31::ZERO
120:             }
121:         });
122:         packed[group] = packed[group].add(qm31_pack_base4(&lanes));
123:     }
124: }
125: 
126: /// Exact linear factoring for a contiguous source-lane interval with one
127: /// common selector:
128: ///
129: /// `pack(s*r0, ..., s*r3) = s*pack(r0, ..., r3)`.
130: ///
131: /// The global source offset may be unaligned, so the first and last groups
132: /// retain the same zero padding as `add_preweighted`.
133: #[inline(always)]
134: #[cfg(any(test, feature = "pool-v1-pair-forest-packed-range-audit"))]
135: fn add_preweighted_shared_selector<const N: usize>(
136:     packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
137:     start: usize,
138:     values: &[QM31; N],
139:     selector: QM31,
140: ) {
141:     let first = start / 4;
142:     let last = (start + N - 1) / 4;
143:     for group in first..=last {
144:         let lanes: [QM31; 4] = core::array::from_fn(|slot| {
145:             let source = 4 * group + slot;
146:             if source >= start && source < start + N {
147:                 values[source - start]
148:             } else {
149:                 QM31::ZERO
150:             }
151:         });
152:         packed[group] = packed[group].add(selector.mul(qm31_pack_base4(&lanes)));
153:     }
154: }
155: 
156: #[inline(always)]
157: fn sum_high(selectors: &Selectors, ranges: &[core::ops::Range<usize>]) -> QM31 {
158:     let mut sum = QM31::ZERO;
159:     for range in ranges {
160:         for block in range.clone() {
161:             sum = sum.add(selectors.high[block]);
162:         }
163:     }
164:     sum
165: }
166: 
167: #[inline(always)]
168: fn reconstruct_10(view: &[QM31; 16]) -> QM31 {
169:     view[..9]
170:         .iter()
171:         .rev()
172:         .fold(view[9], |acc, bit| acc.add(acc).add(*bit))
173: }
174: 
175: #[inline(always)]
176: fn empty_root(level: usize) -> Digest {
177:     constants::POOL_V1_PAIR_EMPTY_ROOTS_V1[level].map(M31)
178: }
179: 
180: fn validate_transition(
181:     public: SemanticPublic<'_>,
182: ) -> Result<(), PoolV1PairForestSemanticTerminalErrorV1> {
183:     let source = public.transition.live_snapshot;
184:     let after = public.transition.candidate_afterstate;
185:     if source.pool != public.pool
186:         || source.deployment_domain != public.deployment_domain
187:         || source.sequence != source.next_pair_index
188:         || source.next_pair_index >= POOL_V1_PAIR_CAPACITY
189:         || source.next_pair_index.checked_add(1) != Some(after.next_pair_index)
190:     {
191:         return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
192:     }
193:     let index = source.next_pair_index;
194:     let carry = core::cmp::min(index.trailing_ones() as usize, 20);
195:     for level in 0..20 {
196:         if level == carry && carry < 20 {
197:             continue;
198:         }
199:         let expected = if level < carry || ((index >> level) & 1) == 0 {
200:             empty_root(level)
201:         } else {
202:             source.frontier[level]
203:         };
204:         if after.next_frontier[level] != expected {
205:             return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidAppendTransition);
206:         }
207:     }
208:     Ok(())
209: }
210: 
211: fn poseidon_selectors(selectors: &Selectors) -> StateOnlyPoseidonSelectors {
212:     StateOnlyPoseidonSelectors {
213:         block: sum_high(selectors, &[0..57]),
214:         local: selectors.low,
215:     }
216: }
217: 
218: #[inline(never)]
219: fn initial_variant_selectors(
220:     variant: CompiledVariant,
221:     high27: QM31,
222:     high28: QM31,
223:     high29: QM31,
224: ) -> (QM31, QM31, QM31, QM31) {
225:     match variant {
226:         CompiledVariant::PrivateTransfer => (
227:             high27,
228:             QM31::ZERO,
229:             high27.add(high28),
230:             high29,
231:         ),
232:         CompiledVariant::Withdrawal => (
233:             QM31::ZERO,
234:             high27.add(high28).add(high29),
235:             QM31::ZERO,
236:             QM31::ZERO,
237:         ),
238:     }
239: }
240: 
241: fn semantic_initial_and_absorption(
242:     public: SemanticPublic<'_>,
243:     openings: &StateOnlyPoseidonOpenings,
244:     selectors: &Selectors,
245: ) -> ([QM31; 16], [QM31; 16]) {
246:     let nodes = sum_high(selectors, &[4..25, 33..57]);
247:     let first_common = selectors.high[0]
248:         .add(selectors.high[1])
249:         .add(selectors.high[25])
250:         .add(selectors.high[30]);
251:     let (transfer_first, fixed, private_chunk_eight, private_chunk_two) =
252:         initial_variant_selectors(
253:             public.variant,
254:             selectors.high[27],
255:             selectors.high[28],
256:             selectors.high[29],
257:         );
258:     let full_initial_selector = selectors.low[0].mul(first_common.add(transfer_first).add(fixed));
259:     let rate_initial_selector = selectors.low[0].mul(nodes);
260:     let full = PreparedQm31Multiplier::new(full_initial_selector);
```

### Lines 316–610
```text
316: fn absorption_lanes_literal(
317:     low: QM31,
318:     fixed: QM31,
319:     chunk_two: QM31,
320:     chunk_eight: QM31,
321:     nodes: QM31,
322:     openings: &[QM31; 16],
323: ) -> [QM31; 16] {
324:     core::array::from_fn(|lane| {
325:         let blocks = if lane < 2 {
326:             fixed
327:         } else if lane < RATE {
328:             fixed.add(chunk_two)
329:         } else {
330:             fixed.add(chunk_two).add(chunk_eight).add(nodes)
331:         };
332:         low.mul(blocks).mul(openings[lane])
333:     })
334: }
335: 
336: #[cfg(any(test, feature = "pool-v1-pair-forest-semantic-factor-audit"))]
337: fn absorption_lanes_factored(
338:     low: QM31,
339:     fixed: QM31,
340:     chunk_two: QM31,
341:     chunk_eight: QM31,
342:     nodes: QM31,
343:     openings: &[QM31; 16],
344: ) -> [QM31; 16] {
345:     let scales = [
346:         PreparedQm31Multiplier::new(low.mul(fixed)),
347:         PreparedQm31Multiplier::new(low.mul(fixed.add(chunk_two))),
348:         PreparedQm31Multiplier::new(low.mul(fixed.add(chunk_two).add(chunk_eight).add(nodes))),
349:     ];
350:     core::array::from_fn(|lane| {
351:         let scale = if lane < 2 {
352:             scales[0]
353:         } else if lane < RATE {
354:             scales[1]
355:         } else {
356:             scales[2]
357:         };
358:         scale.mul(openings[lane])
359:     })
360: }
361: 
362: #[inline(always)]
363: #[cfg(any(test, not(feature = "pool-v1-pair-forest-packed-digest-audit")))]
364: fn add_digest_binding(
365:     output: &mut [QM31; DIGEST_ELEMS],
366:     selector: QM31,
367:     opened: &[QM31; POSEIDON2_WIDTH],
368:     start: usize,
369:     expected: &Digest,
370:     right_tweak: bool,
371: ) {
372:     for lane in 0..DIGEST_ELEMS {
373:         let mut target = expected[lane];
374:         if right_tweak && lane + 1 == DIGEST_ELEMS {
375:             target = target.add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
376:         }
377:         output[lane] = output[lane].add(selector.mul(opened[start + lane].sub(lift_m31(target))));
378:     }
379: }
380: 
381: #[inline(never)]
382: fn add_schedule_lanes(
383:     packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
384:     public: SemanticPublic<'_>,
385:     openings: &StateOnlyPoseidonOpenings,
386:     selectors: &Selectors,
387: ) {
388:     let (initial, absorption) = semantic_initial_and_absorption(public, openings, selectors);
389:     add_preweighted(packed, 0, &initial);
390:     add_preweighted(packed, 16, &absorption);
391: }
392: 
393: #[inline(never)]
394: fn add_path_lanes(
395:     packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
396:     openings: &StateOnlyPoseidonOpenings,
397:     selectors: &Selectors,
398: ) {
399:     let path_selector = sum_high(selectors, &[57..63]).mul(
400:         selectors.low[1]
401:             .add(selectors.low[5])
402:             .add(selectors.low[9])
403:             .add(selectors.low[13]),
404:     );
405:     #[cfg(not(feature = "pool-v1-pair-forest-semantic-factor-audit"))]
406:     let path = path_lanes_literal(path_selector, openings);
407:     #[cfg(feature = "pool-v1-pair-forest-semantic-factor-audit")]
408:     let path = path_lanes_factored(path_selector, openings);
409:     add_preweighted(packed, 32, &path);
410: }
411: 
412: #[cfg(any(test, not(feature = "pool-v1-pair-forest-semantic-factor-audit")))]
413: fn path_lanes_literal(path_selector: QM31, openings: &StateOnlyPoseidonOpenings) -> [QM31; 17] {
414:     let bit = openings.z[0];
415:     let mut path = [QM31::ZERO; 17];
416:     path[0] = path_selector.mul(bit.mul(bit.sub(QM31::ONE)));
417:     for lane in 0..DIGEST_ELEMS {
418:         let current = openings.z[1 + lane];
419:         path[1 + lane] = path_selector
420:             .mul(QM31::ONE.sub(bit))
421:             .mul(openings.succ_z[lane].sub(current));
422:         path[1 + DIGEST_ELEMS + lane] = path_selector
423:             .mul(bit)
424:             .mul(openings.succ_z[RATE + lane].sub(current));
425:     }
426:     path
427: }
428: 
429: #[cfg(any(test, feature = "pool-v1-pair-forest-semantic-factor-audit"))]
430: fn path_lanes_factored(path_selector: QM31, openings: &StateOnlyPoseidonOpenings) -> [QM31; 17] {
431:     let bit = openings.z[0];
432:     let selected_bit = path_selector.mul(bit);
433:     let selected_empty = path_selector.sub(selected_bit);
434:     let left = PreparedQm31Multiplier::new(selected_empty);
435:     let right = PreparedQm31Multiplier::new(selected_bit);
436:     let mut path = [QM31::ZERO; 17];
437:     path[0] = selected_bit.mul(bit.sub(QM31::ONE));
438:     let current0 = openings.z[1];
439:     path[1] = left.mul(openings.succ_z[0].sub(current0));
440:     path[9] = right.mul(openings.succ_z[RATE].sub(current0));
441:     let current1 = openings.z[2];
442:     path[2] = left.mul(openings.succ_z[1].sub(current1));
443:     path[10] = right.mul(openings.succ_z[RATE + 1].sub(current1));
444:     let current2 = openings.z[3];
445:     path[3] = left.mul(openings.succ_z[2].sub(current2));
446:     path[11] = right.mul(openings.succ_z[RATE + 2].sub(current2));
447:     let current3 = openings.z[4];
448:     path[4] = left.mul(openings.succ_z[3].sub(current3));
449:     path[12] = right.mul(openings.succ_z[RATE + 3].sub(current3));
450:     let current4 = openings.z[5];
451:     path[5] = left.mul(openings.succ_z[4].sub(current4));
452:     path[13] = right.mul(openings.succ_z[RATE + 4].sub(current4));
453:     let current5 = openings.z[6];
454:     path[6] = left.mul(openings.succ_z[5].sub(current5));
455:     path[14] = right.mul(openings.succ_z[RATE + 5].sub(current5));
456:     let current6 = openings.z[7];
457:     path[7] = left.mul(openings.succ_z[6].sub(current6));
458:     path[15] = right.mul(openings.succ_z[RATE + 6].sub(current6));
459:     let current7 = openings.z[8];
460:     path[8] = left.mul(openings.succ_z[7].sub(current7));
461:     path[16] = right.mul(openings.succ_z[RATE + 7].sub(current7));
462:     path
463: }
464: 
465: #[inline(never)]
466: fn add_value_lanes(
467:     packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
468:     openings: &StateOnlyPoseidonOpenings,
469:     selectors: &Selectors,
470: ) {
471:     let value_selectors =
472:         [0usize, 2, 4].map(|local| selectors.row(16 * VALUE_AUXILIARY_BLOCK + local));
473:     let range_selector = QM31::ZERO
474:         .add(value_selectors[0])
475:         .add(value_selectors[1])
476:         .add(value_selectors[2]);
477:     let mut range = [QM31::ZERO; 33];
478:     let mut index = 0usize;
479:     while index < 10 {
480:         range[index] = openings.z[index].square().sub(openings.z[index]);
481:         index += 1;
482:     }
483:     index = 0;
484:     while index < 10 {
485:         range[10 + index] = openings.succ_z[index]
486:             .square()
487:             .sub(openings.succ_z[index]);
488:         index += 1;
489:     }
490:     index = 0;
491:     while index < 10 {
492:         range[20 + index] = openings.xor12_z[index]
493:             .square()
494:             .sub(openings.xor12_z[index]);
495:         index += 1;
496:     }
497:     let reconstructed = reconstruct_10(&openings.z)
498:         .add(reconstruct_10(&openings.succ_z).mul_m31(M31(1 << 10)))
499:         .add(reconstruct_10(&openings.xor12_z).mul_m31(M31(1 << 20)));
500:     range[30] = openings.z[10].sub(reconstructed);
501:     range[31] = openings.succ_z[10];
502:     range[32] = openings.xor12_z[10];
503:     #[cfg(not(feature = "pool-v1-pair-forest-packed-range-audit"))]
504:     {
505:         for residual in &mut range {
506:             *residual = range_selector.mul(*residual);
507:         }
508:         add_preweighted(packed, 49, &range);
509:     }
510:     #[cfg(feature = "pool-v1-pair-forest-packed-range-audit")]
511:     add_preweighted_shared_selector(packed, 49, &range, range_selector);
512: 
513:     let conservation_selector = selectors.row(16 * VALUE_AUXILIARY_BLOCK + 6);
514:     let conservation = [
515:         conservation_selector.mul(openings.z[0].sub(openings.z[1]).sub(openings.z[2])),
516:         conservation_selector.mul(openings.succ_z[0].sub(openings.succ_z[1])),
517:     ];
518:     add_preweighted(packed, 82, &conservation);
519: }
520: 
521: #[inline(never)]
522: fn variant_expected_output(variant: CompiledVariant) -> M31 {
523:     match variant {
524:         CompiledVariant::PrivateTransfer => M31(1),
525:         CompiledVariant::Withdrawal => M31(0),
526:     }
527: }
528: 
529: #[inline(never)]
530: fn add_occupancy_lanes(
531:     packed: &mut [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1],
532:     public: SemanticPublic<'_>,
533:     openings: &StateOnlyPoseidonOpenings,
534:     selectors: &Selectors,
535: ) {
536:     let input_occupancy = selectors.row(INPUT_OCCUPANCY_ROW);
537:     let output_occupancy = selectors.row(OUTPUT_OCCUPANCY_ROW);
538:     let expected_output = variant_expected_output(public.variant);
539:     #[cfg(not(feature = "pool-v1-pair-forest-semantic-factor-audit"))]
540:     let occupancy = occupancy_lanes_literal(
541:         input_occupancy,
542:         output_occupancy,
543:         expected_output,
544:         &openings.z,
545:     );
546:     #[cfg(feature = "pool-v1-pair-forest-semantic-factor-audit")]
547:     let occupancy = occupancy_lanes_factored(
548:         input_occupancy,
549:         output_occupancy,
550:         expected_output,
551:         &openings.z,
552:     );
553:     add_preweighted(packed, 0, &occupancy);
554: }
555: 
556: #[cfg(any(test, not(feature = "pool-v1-pair-forest-semantic-factor-audit")))]
557: fn occupancy_lanes_literal(
558:     input_occupancy: QM31,
559:     output_occupancy: QM31,
560:     expected_output: M31,
561:     opened: &[QM31; 16],
562: ) -> [QM31; 12] {
563:     let occupied = opened[0];
564:     let inverse = opened[1];
565:     let one_minus = QM31::ONE.sub(occupied);
566:     let mut occupancy = [QM31::ZERO; 12];
567:     let both = input_occupancy.add(output_occupancy);
568:     occupancy[0] = both.mul(occupied.mul(occupied.sub(QM31::ONE)));
569:     occupancy[1] = both.mul(opened[9].mul(inverse).sub(occupied));
570:     occupancy[2] = both.mul(one_minus.mul(inverse));
571:     for lane in 0..DIGEST_ELEMS {
572:         occupancy[3 + lane] = both.mul(one_minus.mul(opened[2 + lane]));
573:     }
574:     occupancy[11] = input_occupancy
575:         .mul(opened[10].mul(one_minus))
576:         .add(output_occupancy.mul(occupied.sub(lift_m31(expected_output))));
577:     occupancy
578: }
579: 
580: #[cfg(any(test, feature = "pool-v1-pair-forest-semantic-factor-audit"))]
581: fn occupancy_lanes_factored(
582:     input_occupancy: QM31,
583:     output_occupancy: QM31,
584:     expected_output: M31,
585:     opened: &[QM31; 16],
586: ) -> [QM31; 12] {
587:     let occupied = opened[0];
588:     let inverse = opened[1];
589:     let one_minus = QM31::ONE.sub(occupied);
590:     let both = input_occupancy.add(output_occupancy);
591:     let occupied_selector = both.mul(occupied);
592:     let empty_selector = both.sub(occupied_selector);
593:     let empty = PreparedQm31Multiplier::new(empty_selector);
594:     let mut occupancy = [QM31::ZERO; 12];
595:     occupancy[0] = occupied_selector.mul(occupied.sub(QM31::ONE));
596:     occupancy[1] = both.mul(opened[9].mul(inverse).sub(occupied));
597:     occupancy[2] = empty.mul(inverse);
598:     for lane in 0..DIGEST_ELEMS {
599:         occupancy[3 + lane] = empty.mul(opened[2 + lane]);
600:     }
601:     occupancy[11] = input_occupancy
602:         .mul(opened[10].mul(one_minus))
603:         .add(output_occupancy.mul(occupied.sub(lift_m31(expected_output))));
604:     occupancy
605: }
606: 
607: #[inline(never)]
608: #[cfg(any(test, not(feature = "pool-v1-pair-forest-packed-digest-audit")))]
609: fn public_digest_lanes(
610:     public: SemanticPublic<'_>,
```

### Lines 609–735
```text
609: fn public_digest_lanes(
610:     public: SemanticPublic<'_>,
611:     openings: &StateOnlyPoseidonOpenings,
612:     selectors: &Selectors,
613: ) -> [QM31; DIGEST_ELEMS] {
614:     let mut digests = [QM31::ZERO; DIGEST_ELEMS];
615:     add_digest_binding(
616:         &mut digests,
617:         selectors.row(56 * 16 + 11),
618:         &openings.z,
619:         0,
620:         &public.anchor,
621:         false,
622:     );
623:     add_digest_binding(
624:         &mut digests,
625:         selectors.row(26 * 16 + 11),
626:         &openings.z,
627:         0,
628:         &public.nullifier,
629:         false,
630:     );
631:     if let Some(recipient) = public.recipient {
632:         add_digest_binding(
633:             &mut digests,
634:             selectors.row(29 * 16 + 11),
635:             &openings.z,
636:             0,
637:             &recipient,
638:             false,
639:         );
640:     }
641:     add_digest_binding(
642:         &mut digests,
643:         selectors.row(32 * 16 + 11),
644:         &openings.z,
645:         0,
646:         &public.change,
647:         false,
648:     );
649: 
650:     let source = public.transition.live_snapshot;
651:     let after = public.transition.candidate_afterstate;
652:     for level in 0..20 {
653:         let block = 34 + level;
654:         if ((source.next_pair_index >> level) & 1) == 0 {
655:             add_digest_binding(
656:                 &mut digests,
657:                 selectors.row(block * 16),
658:                 &openings.z,
659:                 RATE,
660:                 &empty_root(level),
661:                 true,
662:             );
663:         } else {
664:             add_digest_binding(
665:                 &mut digests,
666:                 selectors.row(block * 16 + 12),
667:                 &openings.z,
668:                 0,
669:                 &source.frontier[level],
670:                 false,
671:             );
672:         }
673:     }
674:     add_digest_binding(
675:         &mut digests,
676:         selectors.row(53 * 16 + 11),
677:         &openings.z,
678:         0,
679:         &after.next_root,
680:         false,
681:     );
682:     let carry = core::cmp::min(source.next_pair_index.trailing_ones() as usize, 20);
683:     if carry < 20 {
684:         add_digest_binding(
685:             &mut digests,
686:             selectors.row((33 + carry) * 16 + 11),
687:             &openings.z,
688:             0,
689:             &after.next_frontier[carry],
690:             false,
691:         );
692:     }
693:     digests
694: }
695: 
696: /// Audit-only form of `public_digest_lanes` after applying the exact identity
697: ///
698: /// `pack(s * d0, ..., s * d3) = s * pack(d0, ..., d3)`.
699: ///
700: /// The two outputs are the unchanged semantic theta lanes 21 and 22.  Keeping
701: /// the literal evaluator above available to tests makes the source-level
702: /// equivalence executable for both variants and every selector point.
703: #[cfg(any(test, feature = "pool-v1-pair-forest-packed-digest-audit"))]
704: #[inline(always)]
705: fn add_digest_binding_packed(
706:     output: &mut [QM31; DIGEST_ELEMS / 4],
707:     selector: QM31,
708:     opened: &[QM31; POSEIDON2_WIDTH],
709:     start: usize,
710:     expected: &Digest,
711:     right_tweak: bool,
712: ) {
713:     for group in 0..DIGEST_ELEMS / 4 {
714:         let residuals: [QM31; 4] = core::array::from_fn(|slot| {
715:             let lane = 4 * group + slot;
716:             let mut target = expected[lane];
717:             if right_tweak && lane + 1 == DIGEST_ELEMS {
718:                 target = target.add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
719:             }
720:             opened[start + lane].sub(lift_m31(target))
721:         });
722:         output[group] = output[group].add(selector.mul(qm31_pack_base4(&residuals)));
723:     }
724: }
725: 
726: #[cfg(any(
727:     test,
728:     all(
729:         feature = "pool-v1-pair-forest-packed-digest-audit",
730:         not(feature = "pool-v1-pair-forest-packed-digest-selector-tensor-audit")
731:     )
732: ))]
733: #[inline(never)]
734: fn public_digest_packed_row_major(
735:     public: SemanticPublic<'_>,
```

### Lines 1110–1439
```text
1110: fn public_digest_packed(
1111:     public: SemanticPublic<'_>,
1112:     openings: &StateOnlyPoseidonOpenings,
1113:     selectors: &Selectors,
1114: ) -> [QM31; DIGEST_ELEMS / 4] {
1115:     #[cfg(not(feature = "pool-v1-pair-forest-packed-digest-selector-tensor-audit"))]
1116:     return public_digest_packed_row_major(public, openings, selectors);
1117:     #[cfg(feature = "pool-v1-pair-forest-packed-digest-selector-tensor-audit")]
1118:     return r20_digest_factored::public_digest_packed_selector_tensor_r20(public, openings, selectors);
1119: }
1120: 
1121: #[inline(never)]
1122: fn scalar_lanes(
1123:     variant: CompiledVariant,
1124:     withdrawal_amount_present: bool,
1125:     input_asset: QM31,
1126:     mut output_scalar: QM31,
1127:     private_transfer_term: QM31,
1128:     withdrawal_term: QM31,
1129: ) -> [QM31; 2] {
1130:     match variant {
1131:         CompiledVariant::PrivateTransfer => {
1132:             output_scalar = output_scalar.add(private_transfer_term);
1133:         }
1134:         CompiledVariant::Withdrawal => {
1135:             if withdrawal_amount_present {
1136:                 output_scalar = output_scalar.add(withdrawal_term);
1137:             }
1138:         }
1139:     }
1140:     [input_asset, output_scalar]
1141: }
1142: 
1143: fn semantic_packed(
1144:     public: SemanticPublic<'_>,
1145:     openings: &StateOnlyPoseidonOpenings,
1146:     selectors: &Selectors,
1147: ) -> [QM31; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1] {
1148:     let mut packed = [QM31::ZERO; POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1];
1149:     add_schedule_lanes(&mut packed, public, openings, selectors);
1150:     add_path_lanes(&mut packed, openings, selectors);
1151:     add_value_lanes(&mut packed, openings, selectors);
1152:     add_occupancy_lanes(&mut packed, public, openings, selectors);
1153:     #[cfg(not(feature = "pool-v1-pair-forest-packed-digest-audit"))]
1154:     add_preweighted(
1155:         &mut packed,
1156:         84,
1157:         &public_digest_lanes(public, openings, selectors),
1158:     );
1159:     #[cfg(feature = "pool-v1-pair-forest-packed-digest-audit")]
1160:     {
1161:         let digests = public_digest_packed(public, openings, selectors);
1162:         packed[84 / 4] = packed[84 / 4].add(digests[0]);
1163:         packed[84 / 4 + 1] = packed[84 / 4 + 1].add(digests[1]);
1164:     }
1165:     let asset_difference = openings.z[1].sub(lift_m31(public.asset_id));
1166:     let input_asset = selectors.row(2 * 16 + 12).mul(asset_difference);
1167:     let output_scalar = selectors.row(31 * 16 + 12).mul(asset_difference);
1168:     let private_transfer_term = selectors.row(28 * 16 + 12).mul(asset_difference);
1169:     let withdrawal_amount_value = public.withdrawal_amount.unwrap_or(0);
1170:     let withdrawal_term = selectors
1171:         .row(16 * VALUE_AUXILIARY_BLOCK + 2)
1172:         .mul(openings.z[10].sub(lift_m31(M31(withdrawal_amount_value))));
1173:     let scalars = scalar_lanes(
1174:         public.variant,
1175:         public.withdrawal_amount.is_some(),
1176:         input_asset,
1177:         output_scalar,
1178:         private_transfer_term,
1179:         withdrawal_term,
1180:     );
1181:     add_preweighted(&mut packed, 92, &scalars);
1182:     packed
1183: }
1184: 
1185: fn selected_claim(
1186:     claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
1187:     point: usize,
1188:     column: usize,
1189: ) -> QM31 {
1190:     claims[point * POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 + column]
1191: }
1192: 
1193: #[inline(never)]
1194: fn copy_variant(variant: CompiledVariant) -> PoolV1PairForestCompiledVariantV1 {
1195:     match variant {
1196:         CompiledVariant::PrivateTransfer => PoolV1PairForestCompiledVariantV1::PrivateTransfer,
1197:         CompiledVariant::Withdrawal => PoolV1PairForestCompiledVariantV1::Withdrawal,
1198:     }
1199: }
1200: 
1201: fn equality_value(left: &[QM31; 10], right: &[QM31; 10]) -> QM31 {
1202:     let factor = |a: QM31, b: QM31| {
1203:         let ab = a.mul(b);
1204:         QM31::ONE.sub(a).sub(b).add(ab).add(ab)
1205:     };
1206:     let mut product = factor(left[0], right[0]);
1207:     let mut index = 1usize;
1208:     while index < left.len() {
1209:         product = product.mul(factor(left[index], right[index]));
1210:         index += 1;
1211:     }
1212:     product
1213: }
1214: 
1215: #[allow(clippy::type_complexity)]
1216: fn composition_parts(
1217:     public: SemanticPublic<'_>,
1218:     claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
1219:     point: &[QM31; 10],
1220:     lambda: QM31,
1221:     chi: QM31,
1222:     theta: QM31,
1223: ) -> Result<
1224:     (
1225:         QM31,
1226:         [QM31; 16],
1227:         [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
1228:         QM31,
1229:         QM31,
1230:         QM31,
1231:     ),
1232:     PoolV1PairForestSemanticTerminalErrorV1,
1233: > {
1234:     if public
1235:         .withdrawal_amount
1236:         .is_some_and(|amount| amount == 0 || amount >= (1 << 30))
1237:     {
1238:         return Err(PoolV1PairForestSemanticTerminalErrorV1::InvalidPublicAmount);
1239:     }
1240:     validate_transition(public)?;
1241:     let openings = StateOnlyPoseidonOpenings {
1242:         z: core::array::from_fn(|column| selected_claim(claims, 0, column)),
1243:         succ_z: core::array::from_fn(|column| selected_claim(claims, 1, column)),
1244:         xor12_z: core::array::from_fn(|column| selected_claim(claims, 2, column)),
1245:     };
1246:     let mask_only = core::array::from_fn(|column| {
1247:         selected_claim(
1248:             claims,
1249:             0,
1250:             POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + column,
1251:         )
1252:     });
1253:     let selectors = Selectors::boxed_at_point(point);
1254:     let poseidon =
1255:         evaluate_state_only_poseidon_oracle_projected(&openings, &poseidon_selectors(&selectors));
1256:     let semantic = semantic_packed(public, &openings, &selectors);
1257:     let h1_z = selected_claim(claims, 0, SELECTED_H1_COLUMN);
1258:     let copy = evaluate_with_selectors(
1259:         &openings.z,
1260:         h1_z,
1261:         &selectors,
1262:         lambda,
1263:         chi,
1264:         public.transition.live_snapshot.next_pair_index,
1265:         copy_variant(public.variant),
1266:     );
1267:     let prepared_theta = PreparedQm31Multiplier::new(theta);
1268:     let mut composition = copy.residual;
1269:     for lane in semantic.into_iter().rev() {
1270:         composition = prepared_theta.mul(composition).add(lane);
1271:     }
1272:     for lane in poseidon.into_iter().rev() {
1273:         composition = prepared_theta.mul(composition).add(lane);
1274:     }
1275:     Ok((
1276:         composition,
1277:         openings.z,
1278:         mask_only,
1279:         selected_claim(claims, 0, SELECTED_G_COLUMN),
1280:         h1_z,
1281:         copy.active,
1282:     ))
1283: }
1284: 
1285: fn terminal_parts(
1286:     public: SemanticPublic<'_>,
1287:     claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
1288:     point: &[QM31; 10],
1289:     lambda: QM31,
1290:     chi: QM31,
1291:     theta: QM31,
1292:     zerocheck_point: &[QM31; 10],
1293:     mu: QM31,
1294: ) -> Result<
1295:     (
1296:         QM31,
1297:         [QM31; 16],
1298:         [QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
1299:         QM31,
1300:     ),
1301:     PoolV1PairForestSemanticTerminalErrorV1,
1302: > {
1303:     let (composition, c1, mask_only, g, h1_z, copy_active) =
1304:         composition_parts(public, claims, point, lambda, chi, theta)?;
1305:     let original = equality_value(zerocheck_point, point)
1306:         .mul(composition)
1307:         .add(mu.mul(h1_z))
1308:         .add(mu.mul(mu).mul(QM31::ONE.sub(copy_active).mul(h1_z)));
1309:     Ok((original, c1, mask_only, g))
1310: }
1311: 
1312: fn private_public<'a>(
1313:     public: &PoolV1PrivateTransferPublicV1,
1314:     transition: &'a PoolV1PairLatePublicStatementV1,
1315: ) -> SemanticPublic<'a> {
1316:     SemanticPublic {
1317:         variant: CompiledVariant::PrivateTransfer,
1318:         pool: public.pool,
1319:         deployment_domain: public.deployment_domain,
1320:         anchor: public.anchor_root,
1321:         nullifier: public.nullifier,
1322:         asset_id: public.asset_id,
1323:         recipient: Some(public.recipient_commitment),
1324:         change: public.change_commitment,
1325:         withdrawal_amount: None,
1326:         transition,
1327:     }
1328: }
1329: 
1330: fn withdrawal_public<'a>(
1331:     public: &PoolV1WithdrawalPublicV1,
1332:     transition: &'a PoolV1PairLatePublicStatementV1,
1333: ) -> SemanticPublic<'a> {
1334:     SemanticPublic {
1335:         variant: CompiledVariant::Withdrawal,
1336:         pool: public.pool,
1337:         deployment_domain: public.deployment_domain,
1338:         anchor: public.anchor_root,
1339:         nullifier: public.nullifier,
1340:         asset_id: public.asset_id,
1341:         recipient: None,
1342:         change: public.change_commitment,
1343:         withdrawal_amount: Some(public.amount),
1344:         transition,
1345:     }
1346: }
1347: 
1348: macro_rules! define_variant_terminal {
1349:     ($composition:ident, $unmasked:ident, $masked:ident, $public_ty:ty, $convert:ident) => {
1350:         #[allow(clippy::too_many_arguments)]
1351:         pub fn $composition(
1352:             public: &$public_ty,
1353:             transition: &PoolV1PairLatePublicStatementV1,
1354:             claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
1355:             point: &[QM31; 10],
1356:             lambda: QM31,
1357:             chi: QM31,
1358:             theta: QM31,
1359:         ) -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
1360:             Ok(composition_parts(
1361:                 $convert(public, transition),
1362:                 claims,
1363:                 point,
1364:                 lambda,
1365:                 chi,
1366:                 theta,
1367:             )?
1368:             .0)
1369:         }
1370: 
1371:         #[allow(clippy::too_many_arguments)]
1372:         pub fn $unmasked(
1373:             public: &$public_ty,
1374:             transition: &PoolV1PairLatePublicStatementV1,
1375:             claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
1376:             point: &[QM31; 10],
1377:             lambda: QM31,
1378:             chi: QM31,
1379:             theta: QM31,
1380:             zerocheck_point: &[QM31; 10],
1381:             mu: QM31,
1382:         ) -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
1383:             Ok(terminal_parts(
1384:                 $convert(public, transition),
1385:                 claims,
1386:                 point,
1387:                 lambda,
1388:                 chi,
1389:                 theta,
1390:                 zerocheck_point,
1391:                 mu,
1392:             )?
1393:             .0)
1394:         }
1395: 
1396:         #[allow(clippy::too_many_arguments)]
1397:         #[inline(never)]
1398:         pub fn $masked(
1399:             public: &$public_ty,
1400:             transition: &PoolV1PairLatePublicStatementV1,
1401:             claims: &[QM31; POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1],
1402:             point: &[QM31; 10],
1403:             lambda: QM31,
1404:             chi: QM31,
1405:             theta: QM31,
1406:             zerocheck_point: &[QM31; 10],
1407:             mu: QM31,
1408:             eta: QM31,
1409:         ) -> Result<QM31, PoolV1PairForestSemanticTerminalErrorV1> {
1410:             let (original, c1, mask_only, g) = terminal_parts(
1411:                 $convert(public, transition),
1412:                 claims,
1413:                 point,
1414:                 lambda,
1415:                 chi,
1416:                 theta,
1417:                 zerocheck_point,
1418:                 mu,
1419:             )?;
1420:             Ok(state_only_selected_mask_value(&c1, &mask_only, g, point).add(eta.mul(original)))
1421:         }
1422:     };
1423: }
1424: 
1425: define_variant_terminal!(
1426:     evaluate_pool_v1_pair_forest_private_transfer_selected_constraint_composition_compiled_v1,
1427:     evaluate_pool_v1_pair_forest_private_transfer_selected_unmasked_terminal_compiled_tag73_v1,
1428:     evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1,
1429:     PoolV1PrivateTransferPublicV1,
1430:     private_public
1431: );
1432: 
1433: define_variant_terminal!(
1434:     evaluate_pool_v1_pair_forest_withdrawal_selected_constraint_composition_compiled_v1,
1435:     evaluate_pool_v1_pair_forest_withdrawal_selected_unmasked_terminal_compiled_tag73_v1,
1436:     evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1,
1437:     PoolV1WithdrawalPublicV1,
1438:     withdrawal_public
1439: );
```
## copy_selector_evaluator — `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs` (SHA256 7371e743a71357f259a58a20c7169188d5c3adb4010c13b6a792c6c65b8cb4a0)

### Lines 130–190
```text
130:             sum.add(values[index])
131:         };
132:         mask &= mask - 1;
133:     }
134:     sum
135: }
136: 
137: #[derive(Clone, Copy)]
138: pub(crate) struct Selectors {
139:     pub(crate) high: [QM31; 64],
140:     pub(crate) low: [QM31; 16],
141: }
142: 
143: impl Selectors {
144:     fn expand<const N: usize>(coordinates: &[QM31]) -> [QM31; N] {
145:         let mut weights = [QM31::ZERO; N];
146:         weights[0] = QM31::ONE;
147:         let mut len = 1usize;
148:         for coordinate in coordinates {
149:             let prepared = PreparedQm31Multiplier::new(*coordinate);
150:             for index in (0..len).rev() {
151:                 let parent = weights[index];
152:                 let right = prepared.mul(parent);
153:                 weights[2 * index] = parent.sub(right);
154:                 weights[2 * index + 1] = right;
155:             }
156:             len *= 2;
157:         }
158:         weights
159:     }
160: 
161:     pub(crate) fn at_point(point: &[QM31; 10]) -> Self {
162:         Self {
163:             high: Self::expand(&point[..6]),
164:             low: Self::expand(&point[6..]),
165:         }
166:     }
167: 
168:     #[inline(never)]
169:     pub(crate) fn boxed_at_point(point: &[QM31; 10]) -> Box<Self> {
170:         Box::new(Self::at_point(point))
171:     }
172: 
173:     #[inline(always)]
174:     pub(crate) fn row(&self, row: usize) -> QM31 {
175:         debug_assert!(row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1);
176:         self.high[row >> 4].mul(self.low[row & 15])
177:     }
178: 
179:     #[cfg(any(test, not(feature = "pool-v1-pair-forest-active-mask-basis-audit")))]
180:     fn active_literal(&self) -> QM31 {
181:         let mut sum = QM31::ZERO;
182:         let mut block = 0usize;
183:         while block < 64 {
184:             let mask = constants::ACTIVE_ROW_MASKS[block];
185:             if mask != 0 {
186:                 sum = sum.add(self.high[block].mul(selector_mask_sum_16(&self.low, mask)));
187:             }
188:             block += 1;
189:         }
190:         sum
```

### Lines 931–1100
```text
931: pub(crate) fn evaluate_with_selectors(
932:     openings: &[QM31; POSEIDON2_WIDTH],
933:     h1_z: QM31,
934:     selectors: &Selectors,
935:     lambda: QM31,
936:     chi: QM31,
937:     append_index: u64,
938:     variant: PoolV1PairForestCompiledVariantV1,
939: ) -> PoolV1PairForestCompiledCopyTerminalV1 {
940:     let patterns = pattern_values(openings, lambda);
941:     let mut row = CopyRowExtension {
942:         producer_values: [QM31::ZERO; 2],
943:         producer_weights: [QM31::ZERO; 2],
944:         consumer_values: [QM31::ZERO; 2],
945:         consumer_weights: [QM31::ZERO; 2],
946:     };
947:     #[cfg(all(
948:         feature = "pool-v1-pair-forest-endpoint-selector-cache-audit",
949:         not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
950:     ))]
951:     let mut selector_cache = EndpointSelectorCache::new();
952:     #[cfg(all(
953:         feature = "pool-v1-pair-forest-copy-pattern-basis-audit",
954:         not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
955:     ))]
956:     let mut tag_values = [QM31::ZERO; 4];
957:     #[cfg(all(
958:         feature = "pool-v1-pair-forest-copy-pattern-basis-audit",
959:         not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
960:     ))]
961:     let mut pattern_selectors = [QM31::ZERO; 26];
962:     #[cfg(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")]
963:     let mut selector_tensor_scratch = vec![QM31::ZERO; COPY_SELECTOR_TENSOR_SCRATCH];
964:     #[cfg(not(all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")))]
965:     {
966:     let mut link_index = 0usize;
967:     while link_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1 {
968:         let link = constants::COPY_LINKS[link_index];
969:         let weight = link_weight(link, append_index, variant);
970:         #[cfg(all(
971:             not(feature = "pool-v1-pair-forest-copy-pattern-basis-audit"),
972:             not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
973:         ))]
974:         #[cfg(not(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit"))]
975:         {
976:             accumulate_endpoint(
977:                 &mut row.producer_values,
978:                 &mut row.producer_weights,
979:                 link.producer,
980:                 link.tag,
981:                 weight,
982:                 &patterns,
983:                 selectors,
984:             );
985:             accumulate_endpoint(
986:                 &mut row.consumer_values,
987:                 &mut row.consumer_weights,
988:                 link.consumer,
989:                 link.tag,
990:                 weight,
991:                 &patterns,
992:                 selectors,
993:             );
994:         }
995:         #[cfg(all(
996:             not(feature = "pool-v1-pair-forest-copy-pattern-basis-audit"),
997:             not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
998:         ))]
999:         #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]
1000:         {
1001:             accumulate_endpoint(
1002:                 &mut row.producer_values,
1003:                 &mut row.producer_weights,
1004:                 link.producer,
1005:                 link.tag,
1006:                 weight,
1007:                 &patterns,
1008:                 selectors,
1009:                 &mut selector_cache,
1010:             );
1011:             accumulate_endpoint(
1012:                 &mut row.consumer_values,
1013:                 &mut row.consumer_weights,
1014:                 link.consumer,
1015:                 link.tag,
1016:                 weight,
1017:                 &patterns,
1018:                 selectors,
1019:                 &mut selector_cache,
1020:             );
1021:         }
1022:         #[cfg(all(
1023:             feature = "pool-v1-pair-forest-copy-pattern-basis-audit",
1024:             not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
1025:         ))]
1026:         {
1027:             accumulate_endpoint_pattern_basis(
1028:                 &mut tag_values,
1029:                 &mut pattern_selectors,
1030:                 &mut row.producer_weights,
1031:                 0,
1032:                 link.producer,
1033:                 link.tag,
1034:                 weight,
1035:                 selectors,
1036:                 #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]
1037:                 &mut selector_cache,
1038:             );
1039:             accumulate_endpoint_pattern_basis(
1040:                 &mut tag_values,
1041:                 &mut pattern_selectors,
1042:                 &mut row.consumer_weights,
1043:                 2,
1044:                 link.consumer,
1045:                 link.tag,
1046:                 weight,
1047:                 selectors,
1048:                 #[cfg(feature = "pool-v1-pair-forest-endpoint-selector-cache-audit")]
1049:                 &mut selector_cache,
1050:             );
1051:         }
1052:         #[cfg(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")]
1053:         {
1054:             accumulate_endpoint_selector_tensor_basis(
1055:                 &mut selector_tensor_scratch,
1056:                 0,
1057:                 link.producer,
1058:                 link.tag,
1059:                 weight,
1060:                 selectors,
1061:             );
1062:             accumulate_endpoint_selector_tensor_basis(
1063:                 &mut selector_tensor_scratch,
1064:                 2,
1065:                 link.consumer,
1066:                 link.tag,
1067:                 weight,
1068:                 selectors,
1069:             );
1070:         }
1071:         link_index += 1;
1072:     }
1073:     }
1074:     #[cfg(all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
1075:     r57_gather(&mut selector_tensor_scratch, selectors, append_index, variant);
1076:     #[cfg(all(
1077:         feature = "pool-v1-pair-forest-copy-pattern-basis-audit",
1078:         not(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")
1079:     ))]
1080:     {
1081:         let values = finish_pattern_basis_values(tag_values, pattern_selectors, &patterns);
1082:         row.producer_values = [values[0], values[1]];
1083:         row.consumer_values = [values[2], values[3]];
1084:     }
1085:     #[cfg(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit")]
1086:     {
1087:         let (values, weights) =
1088:             finish_selector_tensor_basis(&selector_tensor_scratch, &patterns, selectors);
1089:         row.producer_values = [values[0], values[1]];
1090:         row.consumer_values = [values[2], values[3]];
1091:         row.producer_weights = [weights[0], weights[1]];
1092:         row.consumer_weights = [weights[2], weights[3]];
1093:     }
1094:     let active = selectors.active();
1095:     PoolV1PairForestCompiledCopyTerminalV1 {
1096:         residual: active.mul(copy_residual(row, h1_z, chi)),
1097:         active,
1098:     }
1099: }
1100: 
```
## state_only_mask — `crates/aspis-core/src/state_only_hiding.rs` (SHA256 18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f)

### Lines 570–665
```text
570:         c1,
571:         mask_only_c1: core::array::from_fn(|column| {
572:             mul_tower_basis(
573:                 powers[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])],
574:                 column & 3,
575:             )
576:         }),
577:         explicit_g: QM31::ONE
578:             .add(mask_linear(EXPLICIT_FACTOR_FAMILY, point).pow(EXPLICIT_FACTOR_EXPONENT as u64)),
579:     }
580: }
581: 
582: pub fn state_only_c1_mask_factor(
583:     column: usize,
584:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
585: ) -> QM31 {
586:     assert!(column < STATE_ONLY_HIDING_C1_COLUMNS);
587:     let family = usize::from(FACTOR_FAMILIES[column]);
588:     let exponent = usize::from(FACTOR_EXPONENTS[column]);
589:     state_only_mask_tower_basis(column & 3).mul(mask_power(mask_linear(family, point), exponent))
590: }
591: 
592: pub fn state_only_explicit_g_mask_factor(
593:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
594: ) -> QM31 {
595:     explicit_mask_factor(point)
596: }
597: 
598: /// Degree-at-most-26 factors for the ten selected full-domain M31 mask-only
599: /// columns. They use the rank-pinned unused odd powers of the same dense
600: /// linear form as the semantic columns, with distinct tower rotations.
601: pub fn state_only_mask_only_c1_factor(
602:     mask_column: usize,
603:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
604: ) -> QM31 {
605:     assert!(mask_column < STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS);
606:     let exponent = usize::from(MASK_ONLY_FACTOR_EXPONENTS[mask_column]);
607:     mul_tower_basis(mask_power(mask_linear(0, point), exponent), mask_column & 3)
608: }
609: 
610: /// Evaluate the exact degree-at-most-27 mask polynomial terminal from the 16
611: /// already PCS-bound base-column evaluations and one explicit QM31 mask.
612: pub fn state_only_mask_value_with_factors(
613:     c1: &[QM31; STATE_ONLY_HIDING_C1_COLUMNS],
614:     explicit_g: QM31,
615:     factors: &StateOnlyMaskFactors,
616: ) -> QM31 {
617:     c1.iter()
618:         .copied()
619:         .zip(factors.c1)
620:         .fold(QM31::ZERO, |sum, (value, factor)| {
621:             sum.add(factor.mul(value))
622:         })
623:         .add(factors.explicit_g.mul(explicit_g))
624: }
625: 
626: pub fn state_only_mask_value(
627:     c1: &[QM31; STATE_ONLY_HIDING_C1_COLUMNS],
628:     explicit_g: QM31,
629:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
630: ) -> QM31 {
631:     state_only_mask_value_with_factors(c1, explicit_g, &state_only_mask_factors(point))
632: }
633: 
634: pub fn state_only_selected_mask_value_with_factors(
635:     c1: &[QM31; STATE_ONLY_HIDING_C1_COLUMNS],
636:     mask_only_c1: &[QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
637:     explicit_g: QM31,
638:     factors: &StateOnlyMaskFactors,
639: ) -> QM31 {
640:     mask_only_c1.iter().copied().zip(factors.mask_only_c1).fold(
641:         state_only_mask_value_with_factors(c1, explicit_g, factors),
642:         |sum, (value, factor)| sum.add(factor.mul(value)),
643:     )
644: }
645: 
646: #[inline(never)]
647: pub fn state_only_selected_mask_value(
648:     c1: &[QM31; STATE_ONLY_HIDING_C1_COLUMNS],
649:     mask_only_c1: &[QM31; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS],
650:     explicit_g: QM31,
651:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
652: ) -> QM31 {
653:     let (linear, explicit_linear) = selected_mask_linears(point);
654:     let mut coefficients = [QM31::ZERO; STATE_ONLY_HIDING_FACTOR_DEGREE + 1];
655:     for column in 0..STATE_ONLY_HIDING_C1_COLUMNS {
656:         coefficients[usize::from(FACTOR_EXPONENTS[column])] =
657:             mul_tower_basis(c1[column], column & 3);
658:     }
659:     for column in 0..STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS {
660:         coefficients[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])] =
661:             mul_tower_basis(mask_only_c1[column], column & 3);
662:     }
663: 
664:     let prepared_linear = PreparedQm31Multiplier::new(linear);
665:     let mut shared = coefficients[STATE_ONLY_HIDING_FACTOR_DEGREE];
```
## poseidon_projected — `crates/aspis-statement/src/state_only_poseidon.rs` (SHA256 4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe)

### Lines 575–625
```text
575:     })
576: }
577: 
578: /// Exact packed-projection implementation of [`evaluate_state_only_poseidon_oracle`].
579: ///
580: /// Only the two full/full branches benefit: their second external layer is
581: /// consumed through its four packed adjoint functionals.  The internal branch
582: /// remains on the original path because a generic adjoint there would replace
583: /// additions by sixteen extension-field products.
584: #[inline(never)]
585: pub fn evaluate_state_only_poseidon_oracle_projected(
586:     openings: &StateOnlyPoseidonOpenings,
587:     selectors: &StateOnlyPoseidonSelectors,
588: ) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
589:     let leading_low = selectors.local[0];
590:     let full_low = [1usize, 9, 10]
591:         .into_iter()
592:         .fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
593:     let internal_low = (2usize..=8).fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
594:     let leading = leading_pair_packed(openings);
595:     let full = interpolated_full_pair_packed(openings.z, &selectors.local);
596:     let internal = interpolated_internal_pair(openings.z, &selectors.local);
597:     let prepared_weights = [leading_low, full_low, internal_low].map(PreparedQm31Multiplier::new);
598:     let prepared_block = PreparedQm31Multiplier::new(selectors.block);
599: 
600:     core::array::from_fn(|group| {
601:         let start = 4 * group;
602:         let target = qm31_pack_base4(&openings.succ_z[start..start + 4]);
603:         let internal = qm31_pack_base4(&internal[start..start + 4]);
604:         // `active_low = leading_low + full_low + internal_low`, so the
605:         // four-product residual is exactly three weighted differences. This
606:         // removes one QM31 product per packed group without changing the
607:         // polynomial or its selector basis.
608:         prepared_block.mul(qm31_sum_products3_prepared(
609:             &prepared_weights,
610:             &[
611:                 target.sub(leading[group]),
612:                 target.sub(full[group]),
613:                 target.sub(internal),
614:             ],
615:         ))
616:     })
617: }
618: 
619: fn multilinear_evaluate(column: &[M31], point: &[QM31; 10]) -> Option<QM31> {
620:     if column.len() != STATE_ONLY_POSEIDON_TRACE_ROWS {
621:         return None;
622:     }
623:     let mut layer = column.iter().copied().map(lift).collect::<Vec<_>>();
624:     let mut width = layer.len();
625:     for coordinate in point.iter().rev() {
```
## performance_verifier — `docs/research/v8-no-work-100-20260907/experiments/performance_verifier.rs` (SHA256 d6dad89eaa8d735f467055e96a8df12de7a391e2475ec26c44b2bc493624a62a)

### Lines 20–135
```text
20:     out
21: }
22: #[cfg(v8_semantic_carry)]
23: #[inline(never)]
24: fn semantic_eval(poly:&[K;28],alpha:K)->K {super::semantic_carry::evaluate(poly,alpha)}
25: pub(super) fn checkpoint(name:&str){
26:     #[cfg(all(v8_performance_sbf,not(v8_quiet_profile)))] {
27:         ();
28:         ();
29:     }
30:     #[cfg(any(not(v8_performance_sbf),v8_quiet_profile))] let _=name;
31: }
32: #[inline(never)]
33: fn semantic(w:&Wire<'_>,binding:&[u8;32],public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1)->Result<row::Semantic,Error>{
34:     semantic_cached(w,binding,public,transition,&mut [])
35: }
36: #[inline(never)]
37: fn semantic_cached(w:&Wire<'_>,binding:&[u8;32],public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1,cache:&mut[K])->Result<row::Semantic,Error>{
38:     assert!(cache.is_empty() || cache.len()==271);
39:     let mut t=Transcript::new(hash);t.absorb(label::PROFILE,b"AV8/R102/sparseG-bitperm-two-swaps/quadratic-channel-fold/merkle8-research-v1");
40:     #[cfg(v8_positive_transfer)] super::positive_transfer::absorb(&mut t);
41:     t.absorb(label::PROFILE,b"AV8/payment-extraction/v1");
42:     t.absorb(label::STATEMENT,binding);t.absorb(label::ROOT,&w.roots.0);
43:     let lambda=sample(&mut t,false)?;let chi=sample(&mut t,false)?;
44:     t.absorb(label::SECOND_PHASE_ROOT,&w.roots.1);
45:     let bat=begin_state_only_zerocheck(&mut t).map_err(|_|Error::Sampler)?;
46:     let eta=begin_state_only_masked_sumcheck(&mut t,w.v[0]).map_err(|_|Error::Sampler)?;
47:     let mut s=row::Semantic{t,z:[K::ZERO;10],lambda,chi,theta:bat.theta,zc:bat.zerocheck_point,mu:bat.mu,eta,claim:w.v[0]};
48:     for r in 0..10 {
49:         let sent=&w.v[1+27*r..1+27*(r+1)];
50:         let mut record=vec![r as u8];record.extend(bytes(sent));
51:         s.t.absorb(label::V6_COMPACT_SEMANTIC_ROUND,&record);
52:         s.z[r]=sample(&mut s.t,false)?;
53:         if cache.is_empty() {
54:         let mut poly=[K::ZERO;28];poly[0]=sent[0];poly[2..].copy_from_slice(&sent[1..]);
55:         #[cfg(not(v8_semantic_boundary))]
56:         {poly[1]=s.claim.sub(poly[0].add(poly[0]).add(poly[2..].iter().copied().fold(K::ZERO,|a,b|a.add(b))));}
57:         #[cfg(v8_semantic_boundary)]
58:         {poly[1]=super::semantic_boundary::missing(s.claim,poly[0],poly[2..].try_into().unwrap());}
59:             #[cfg(not(v8_block_horner))] {s.claim=evaluate_state_only_polynomial(&poly,s.z[r]);}
60:             #[cfg(v8_block_horner)] {s.claim=semantic_eval(&poly,s.z[r]);}
61:         } else {
62:             // Cache is verifier-owned and freshly derived AFTER this round's challenge.
63:             #[cfg(not(target_os="solana"))] let old_claim=s.claim;
64:             s.claim=crate::r20_semantic_basis::evaluate_round(s.claim,sent.try_into().unwrap(),s.z[r],
65:                 (&mut cache[1+27*r..1+27*(r+1)]).try_into().unwrap());
66:             #[cfg(not(target_os="solana"))] {
67:         let mut poly=[K::ZERO;28];poly[0]=sent[0];poly[2..].copy_from_slice(&sent[1..]);
68:         #[cfg(not(v8_semantic_boundary))]
69:         {poly[1]=old_claim.sub(poly[0].add(poly[0]).add(poly[2..].iter().copied().fold(K::ZERO,|a,b|a.add(b))));}
70:         #[cfg(v8_semantic_boundary)]
71:         {poly[1]=super::semantic_boundary::missing(old_claim,poly[0],poly[2..].try_into().unwrap());}
72:             assert_eq!(s.claim,evaluate_state_only_polynomial(&poly,s.z[r]));
73:             }
74:         }
75:     }
76:     if !cache.is_empty() {
77:         for r in (0..10).rev() {
78:             for v in &mut cache[1+27*r..1+27*(r+1)] {
79:                 *v=crate::r20_semantic_basis::scale_power_of_two(*v,9-r);
80:             }
81:         }
82:         cache[0]=crate::r20_semantic_basis::scale_power_of_two(K::ONE,10);
83:         #[cfg(not(target_os="solana"))] {
84:             let mut original=vec![K::ZERO;271];
85:             crate::r18_sparse_coded_g::coin_weights_into(&s.z,&mut original);
86:             assert_eq!(cache,original.as_slice(),"actual ten-challenge G cache");
87:         }
88:     }
89:     checkpoint("v8:semantic-rounds");
90:     let claims:[K;84]=std::array::from_fn(|i|w.v[271+(i/28)*29+i%28]);
91:     let actual=payment_terminal(public,transition,&claims,&s.z,&s)?;
92:     if actual!=s.claim{return Err(Error::Terminal);}
93:     checkpoint("v8:semantic-terminal");
94:     #[cfg(v8_semantic_control)] {
95:         // Matched selected V7 terminal call: same literal 3x28 projection and
96:         // all public/challenge inputs. Diagnostic duplicate, NOT a saving.
97:         let again=payment_terminal(public,transition,&claims,&s.z,&s)?;
98:         if again!=actual{return Err(Error::Terminal);}
99:         checkpoint("v8:selected-semantic-control");
100:     }
101:     Ok(s)
102: }
103: #[cfg(v8_semantic_control)]
104: #[inline(never)]
105: fn selected_terminal_control(public:&PoolV1PrivateTransferPublicV1,transition:&PoolV1PairLatePublicStatementV1,claims:&[K;84],s:&row::Semantic)->Result<K,Error>{
106:     evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(
107:         public,transition,claims,&s.z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta).map_err(|_|Error::Terminal)
108: }
109: /// Codes are research diagnostics, never production acceptance/status codes.
110: #[inline(never)]
111: fn semantic_bytes(w:&Wire<'_>,binding:&[u8;32],public:&[u8],transition:&[u8])->Result<row::Semantic,u32>{
112:     let public=decode_pool_v1_private_transfer_public_v1(public).map_err(|_|1u32)?;
113:     let transition=decode_pool_v1_pair_late_public_statement_v1(transition).map_err(|_|2u32)?;
114:     semantic(w,binding,&PoolV1PairForestTerminalPaymentV1::PrivateTransfer(public),&transition).map_err(|_|4u32)
115: }
116: #[cfg_attr(v8_semantic_stack,inline(never))]
117: pub(super) fn payment_terminal(public:&PoolV1PairForestTerminalPaymentV1,transition:&PoolV1PairLatePublicStatementV1,claims:&[K;84],z:&[K;10],s:&row::Semantic)->Result<K,Error>{
118:     #[cfg(v8_positive_transfer)]
119:     if !matches!(public,PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)){return Err(Error::Shape);}
120:     let value=match public {
121:         PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=>
122:             evaluate_pool_v1_pair_forest_private_transfer_selected_masked_terminal_compiled_tag73_v1(p,transition,claims,z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta),
123:         PoolV1PairForestTerminalPaymentV1::Withdrawal(p)=>
124:             evaluate_pool_v1_pair_forest_withdrawal_selected_masked_terminal_compiled_tag73_v1(p,transition,claims,z,s.lambda,s.chi,s.theta,&s.zc,s.mu,s.eta),
125:     }.map_err(|_|Error::Terminal)?;
126:     let value=value.sub(claims[27].mul(corelib::state_only_hiding::state_only_explicit_g_mask_factor(z))).add(claims[27]);
127: 
128:     #[cfg(v8_positive_transfer)]
129:     return Ok(value.add(super::positive_transfer::terminal_delta(claims,z,s.theta,&s.zc,s.eta)));
130:     #[cfg(not(v8_positive_transfer))] Ok(value)
131: }
132: #[inline(never)]
133: pub fn verify(body:&[u8],binding:&[u8;32],public:&[u8],transition:&[u8])->Result<(),u32>{
134: 
135: #[cfg(target_os="solana")] { (); (); }
```
## positive_transfer — `docs/research/v8-no-work-100-20260907/experiments/positive_transfer.rs` (SHA256 3a19043d2f40f168cb2127ba46e1795db7ea0751625c4fe48c73e02dab533cab)

### Lines 1–14
```text
1: //! Opt-in research design change: selected transfer output positivity.
2: //! No production feature enables this module. The legacy mask generator's
3: //! draw order is retained; its active-row1014/c3 draw is discarded before C1.
4: //! New transcript framing binds this adapter, not a claim of unchanged ZK.
5: use super::*;
6: use aspis_statement::pool_v1::*;
7: #[cfg(not(v8_performance_sbf))] use aspis_statement::StateOnlyTraceFoundation;
8: #[cfg(not(v8_performance_sbf))]
9: #[path="selected_transfer_zero.rs"] mod zero_fixture;
10: 
11: pub const ROW: usize = 1014;
12: pub const COL: usize = 3;
13: pub const LANE: usize = 94;
14: pub const PROFILE: &[u8] = b"AV8/positive-transfer/active-cell-overwrite/lane94/v1";
```

### Lines 72–98
```text
72: pub fn residual(claims:&[K;84])->K{
73:     claims[1].mul(claims[28+1]).mul(claims[COL]).sub(K::ONE)
74: }
75: pub fn selector(z:&[K;10])->K{
76:     z.iter().enumerate().fold(K::ONE,|a,(j,x)|a.mul(
77:         if (ROW>>(9-j))&1==1 {*x} else {K::ONE.sub(*x)}))
78: }
79: pub fn equality(z:&[K;10],zc:&[K;10])->K{
80:     z.iter().zip(zc).fold(K::ONE,|p,(a,b)|{
81:         let ab=a.mul(*b);p.mul(K::ONE.sub(*a).sub(*b).add(ab).add(ab))})
82: }
83: pub fn composition_delta(claims:&[K;84],z:&[K;10],theta:K)->K{
84:     // Source lane94 = packed group23, limb2; after four Poseidon lanes it
85:     // has theta exponent27. Do not treat extension-valued packing as casts.
86:     let weighted=selector(z).mul(residual(claims));
87:     let packed=corelib::field::qm31_pack_base4(&[K::ZERO,K::ZERO,weighted,K::ZERO]);
88:     let t2=theta.square();let t4=t2.square();let t8=t4.square();let t16=t8.square();
89:     t16.mul(t8).mul(t2).mul(theta).mul(packed)
90: }
91: pub fn terminal_delta(claims:&[K;84],z:&[K;10],theta:K,zc:&[K;10],eta:K)->K{
92:     eta.mul(equality(z,zc).mul(composition_delta(claims,z,theta)))
93: }
94: 
95: #[cfg(not(v8_performance_sbf))]
96: pub fn layout_control(){
97:     let old=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();let new=mask_cells();
98:     assert_eq!(fingerprint(&old),pool_v1_pair_forest_relation_free_mask_fingerprint_v1().unwrap());
```
## Lean `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/SourceStatementPoints.lean` (SHA256 418236a0c336733d73f41d151b5d010a241649eaa4fb9f06d43e842dcf0ca447)

### Lines 1–56
```lean
1: import AspisV8R19.FullWitnessPointCode
2: 
3: /-! Exact-field v6_statement_points, including the special last-coordinate
4: initialization and the descending carry updates. Ten symbolic factors only. -/
5: namespace AspisR19.SourceStatementPoints
6: noncomputable section
7: variable {F : Type*} [CommRing F]
8: 
9: def reverseCoordinates : List (Fin 10) := [8,7,6,5,4,3,2,1,0]
10: 
11: theorem coordinates_eq : reverseCoordinates=
12:     ((List.finRange 9).reverse.map (fun i => (⟨i.val,by omega⟩ : Fin 10))) := by decide
13: 
14: def step (z : Fin 10 → F) (state : F × (Fin 10 → F)) (i : Fin 10) : F × (Fin 10 → F) :=
15:   let bc := z i*state.1
16:   (bc,Function.update state.2 i (z i+state.1-(bc+bc)))
17: 
18: def successor (z : Fin 10 → F) : Fin 10 → F :=
19:   (reverseCoordinates.foldl (step z) (z 9,Function.update z 9 (1-z 9))).2
20: 
21: theorem successor_eq (z : Fin 10 → F) (i : Fin 10) :
22:     successor z i=ResidualModel.point z 1 i := by
23:   fin_cases i <;>
24:     simp [successor,reverseCoordinates,step,ResidualModel.point,ResidualModel.carry,Fin.prod_univ_succ] <;> ring
25: 
26: def xor12 (z : Fin 10 → F) : Fin 10 → F :=
27:   ([7,6] : List (Fin 10)).foldl (fun out i => Function.update out i (1-out i)) z
28: 
29: theorem xor12_eq (z : Fin 10 → F) (i : Fin 10) : xor12 z i=ResidualModel.point z 2 i := by
30:   fin_cases i <;> simp [xor12,ResidualModel.point]
31: 
32: def points (z : Fin 10 → F) (which : Fin 3) : Fin 10 → F :=
33:   if which=0 then z else if which=1 then successor z else xor12 z
34: 
35: theorem points_eq (z : Fin 10 → F) (which : Fin 3) :
36:     points z which=ResidualModel.point z which.val := by
37:   funext i
38:   fin_cases which
39:   · simp [points,ResidualModel.point]
40:   · simpa [points] using successor_eq z i
41:   · simpa [points] using xor12_eq z i
42: 
43: #print axioms coordinates_eq
44: #print axioms successor_eq
45: #print axioms xor12_eq
46: #print axioms points_eq
47: end
48: end AspisR19.SourceStatementPoints
```
## Lean `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/ResidualDegree.lean` (SHA256 8822dd90f58ced4bb84ee678617e616689e484081ead5d5d4f8db51cf2c4960e)

### Lines 35–112
```lean
35:   split_ifs <;> simp
36: 
37: theorem chord_degree (half : F) (a b c : Poly (F:=F)) (d j r : Nat)
38:     (ha : a.totalDegree ≤ d) (hb : b.totalDegree ≤ d) (hc : c.totalDegree ≤ d) :
39:     (chordEntry (C half) a b c j r).totalDegree ≤ d := by
40:   unfold chordEntry
41:   split_ifs
42:   · exact add_bound (mul_constant ha (delta_degree _ _)) (mul_constant hb (x_degree _ _ _))
43:   · exact mul_constant hc (delta_degree _ _)
44:   · exact mul_constant hc (sub_bound (delta_degree _ _) (xx_degree _ _ _))
45:   · exact add_bound (mul_constant ha (delta_degree _ _)) (mul_constant hb (x_degree _ _ _))
46: 
47: theorem carry_degree (z : Fin 10 → Poly (F:=F))
48:     (hz : ∀ i, (z i).totalDegree ≤ 1) (i : Fin 10) :
49:     (carry z i).totalDegree ≤ 9-i.val := by
50:   unfold carry
51:   apply (totalDegree_finsetProd _ _).trans
52:   calc
53:     _ ≤ ∑ k : Fin 10, (if i.val<k.val then 1 else 0 : Nat) := by
54:       apply Finset.sum_le_sum
55:       intro k _
56:       split_ifs <;> simp_all
57:     _ = 9-i.val := by fin_cases i <;> decide
58: 
59: theorem point_degree (z : Fin 10 → Poly (F:=F))
60:     (hz : ∀ i, (z i).totalDegree ≤ 1) (which : Nat) (i : Fin 10) :
61:     (point z which i).totalDegree ≤ 10-i.val := by
62:   have hi : 1 ≤ 10-i.val := by omega
63:   have hc := carry_degree z hz i
64:   have htwo : ((2:Poly (F:=F))*z i*carry z i).totalDegree ≤ 10-i.val := by
65:     have hm := mul_bound (show (2:Poly (F:=F)).totalDegree ≤ 0 by
66:       change (C (2:F)).totalDegree ≤ 0
67:       simp) (hz i)
68:     exact (mul_bound hm hc).trans (by omega)
69:   unfold point
70:   split_ifs
71:   · exact (hz i).trans hi
72:   · exact sub_bound (add_bound ((hz i).trans hi) (hc.trans (by omega))) htwo
73:   · exact sub_bound (by simp) ((hz i).trans hi)
74:   · exact (hz i).trans hi
75: 
76: theorem tensor_degree (z : Fin 10 → Poly (F:=F))
77:     (hz : ∀ i, (z i).totalDegree ≤ 10-i.val) (r : Nat) :
78:     (tensor z r).totalDegree ≤ 55 := by
79:   unfold tensor
80:   apply (totalDegree_finsetProd _ _).trans
81:   calc
82:     _ ≤ ∑ i : Fin 10, (10-i.val) := by
83:       apply Finset.sum_le_sum
84:       intro i _
85:       split_ifs
86:       · exact sub_bound (by simp) (hz i)
87:       · exact hz i
88:     _ = 55 := by decide
89: 
90: theorem code_degree (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
91:     (z : Fin 10 → Poly (F:=F)) (hz : ∀ i, (z i).totalDegree ≤ 10-i.val) (j : Fin 111) :
92:     (codeWeight order inactive z j).totalDegree ≤ 55 := by
93:   unfold codeWeight
94:   apply sub_bound (tensor_degree z hz _)
95:   split_ifs
96:   · exact tensor_degree z hz _
97:   · simp
98: 
99: theorem point_weight_degree (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
100:     (half : F) (a b c : Poly (F:=F)) (z : Fin 10 → Poly (F:=F))
101:     (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2)
102:     (hz : ∀ i, (z i).totalDegree ≤ 1) (which r : Nat) :
103:     (pointWeight order inactive (C half) a b c z which r).totalDegree ≤ 57 := by
104:   apply totalDegree_finsetSum_le
105:   intro j _
106:   exact mul_bound (code_degree order inactive _ (point_degree z hz which) j)
107:     (chord_degree half a b c 2 r j.val ha hb hc)
108: 
109: theorem shift_degree (half : F) (n : Nat) (p : Fin 27 → Poly (F:=F)) (d : Nat)
110:     (hp : ∀ j, (p j).totalDegree ≤ d) (r : Fin 27) :
111:     (shift (C half) n p r).totalDegree ≤ d := by
112:   induction n generalizing r with
```
## Lean `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/FixedQueryDegree.lean` (SHA256 d2e927044451ccb635fce80e486612085ed2fb7c7afdfb62302e99994d3ff303)

### Lines 1–78
```lean
1: import AspisV8R19.FixedQueryPolynomial
2: import AspisV8R19.ResidualDegree
3: 
4: /-! Degree for the new fixed-query polynomial, not the old 111-coordinate
5: minor. Query-section coefficients are constants; the G boundary is retained. -/
6: namespace AspisR19.FixedQueryDegree
7: open MvPolynomial ResidualDegree HighRepairInvariant BetaUniformCorrection
8: noncomputable section
9: variable {F : Type*} [CommRing F]
10: 
11: theorem full_code_degree (z : Fin 10 → Poly (F:=F))
12:     (hz : ∀ i, (z i).totalDegree ≤ 1) (which : Nat) (j : Fin 131) :
13:     (FullPointFunctional.codeWeight
14:       (fun r => AspisV8R17.sourcePointBasis (ResidualModel.point z which) r.val) j).totalDegree ≤ 55 := by
15:   simp only [FullPointFunctional.codeWeight,FullPointFunctional.source_tensor]
16:   apply sub_bound (tensor_degree _ (point_degree z hz which) _)
17:   split_ifs
18:   · exact tensor_degree _ (point_degree z hz which) _
19:   · simp
20: 
21: theorem point_weight_degree (half : F) (a b c : Poly (F:=F)) (z : Fin 10 → Poly (F:=F))
22:     (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2)
23:     (hz : ∀ i, (z i).totalDegree ≤ 1) (which : Nat) (i : Index 32) :
24:     (FixedQueryModel.pointWeight (C half) a b c z which i).totalDegree ≤ 57 := by
25:   apply totalDegree_finsetSum_le
26:   intro j _
27:   exact mul_bound (full_code_degree z hz which j)
28:     (chord_degree half a b c 2 _ j.val ha hb hc)
29: 
30: theorem g_degree (half : F) (a b c : Poly (F:=F))
31:     (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2) (i : Index 32) :
32:     (FixedQueryModel.gBoundary (C half) a b c i).totalDegree ≤ 2 := by
33:   unfold FixedQueryModel.gBoundary
34:   exact (mul_bound (by simpa only [totalDegree_C,mul_zero] using
35:       (totalDegree_pow (C half : Poly) 10) : ((C half : Poly)^10).totalDegree ≤ 0)
36:     (chord_degree half a b c 2 _ 128 ha hb hc)).trans (by decide)
37: 
38: theorem weight_degree (half : F) (a b c kappa : Poly (F:=F)) (z : Fin 10 → Poly (F:=F))
39:     (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2)
40:     (hk : kappa.totalDegree ≤ 1) (hz : ∀ i, (z i).totalDegree ≤ 1)
41:     (structured : Bool) (i : Index 32) :
42:     (FixedQueryModel.weight (C half) a b c kappa z structured i).totalDegree ≤ 60 := by
43:   have he := point_weight_degree half a b c z ha hb hc hz
44:   have hkpow (n : Nat) : (kappa^n).totalDegree ≤ n :=
45:     (totalDegree_pow _ _).trans (by nlinarith)
46:   unfold FixedQueryModel.weight
47:   apply add_bound
48:   · apply add_bound
49:     · apply (mul_bound hk ?_).trans (by decide : 1+57≤60)
50:       cases structured
51:       · exact he 0 i
52:       · exact (g_degree half a b c ha hb hc i).trans (by decide)
53:     · exact (mul_bound (hkpow 2) (he 1 i)).trans (by decide)
54:   · exact mul_bound (hkpow 3) (he 2 i)
55: 
56: theorem column_degree (v : Fin 13 → Fin 32 → F) (alpha : Poly (F:=F))
57:     (ha : alpha.totalDegree ≤ 1) (j : Fin 13) (i : Index 32) :
58:     (FixedQueryModel.column (fun j i => C (v j i)) alpha j i).totalDegree ≤ 3 := by
59:   have hp : (alpha^(SparseHighWitness.slot j).val).totalDegree ≤ 3 :=
60:     (totalDegree_pow _ _).trans (by have := (SparseHighWitness.slot j).isLt; nlinarith)
61:   unfold FixedQueryModel.column
62:   apply (mul_bound (by simp : (C (v j i.1) : Poly).totalDegree ≤ 0) ?_).trans (by decide : 0+3≤3)
63:   apply sub_bound
64:   · split_ifs <;> simp
65:   · apply mul_constant hp
66:     split_ifs <;> simp
67: 
68: theorem coefficient_degree (quarter : F) (q w : Index 32 → Poly (F:=F))
69:     (hq : ∀ i, (q i).totalDegree ≤ 3) (hw : ∀ i, (w i).totalDegree ≤ 60) (k : Nat) :
70:     (coefficient (sourceKernel 32 k (C quarter)) q w).totalDegree ≤ 63 := by
71:   apply totalDegree_finsetSum_le
72:   intro i _
73:   apply totalDegree_finsetSum_le
74:   intro j _
75:   have hk : (sourceKernel 32 k (C quarter : Poly) i j).totalDegree ≤ 0 := by
76:     unfold sourceKernel
77:     split_ifs <;> simp
78:   exact mul_bound (mul_bound hk (hq i)) (hw j)
```
## Lean `docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/SourceResidualDegree.lean` (SHA256 202f5e09b3451e76ba3e7828ec1110bb0bd67ca07a8c4542ac47640bb46371d6)

### Lines 1–55
```lean
1: /- Total degree after the actual algebraic substitutions, not an IID theorem. -/
2: import AspisV8R19.ResidualDegree
3: 
4: namespace AspisR19.SourceResidualDegree
5: open MvPolynomial ResidualModel SourceResidualPolynomial ResidualDegree
6: variable {F : Type*} [CommRing F]
7: noncomputable section
8: 
9: theorem observation_degree (order : Fin 111 → Nat) (inactive : Fin 111 → Bool)
10:     (half quarter : F) (a b c κ alpha : Poly (F:=F))
11:     (z : Fin 10 → Poly (F:=F)) (p : Fin 23 → Poly (F:=F))
12:     (ha : a.totalDegree ≤ 2) (hb : b.totalDegree ≤ 2) (hc : c.totalDegree ≤ 2)
13:     (hk : κ.totalDegree ≤ 1) (halpha : alpha.totalDegree ≤ 1)
14:     (hz : ∀ i, (z i).totalDegree ≤ 1) (hp : ∀ j, (p j).totalDegree ≤ 22)
15:     (row : Nat) (col : Fin 13) :
16:     (observation order inactive (C half) (C quarter) a b c κ alpha z p row col).totalDegree ≤ 85 := by
17:   let e := fun which (r : Fin 108) => pointWeight order inactive (C half) a b c z which r.val
18:   have he (which : Nat) (r : Fin 108) : (e which r).totalDegree ≤ 57 :=
19:     point_weight_degree order inactive half a b c z ha hb hc hz which r.val
20:   have hq (r : Fin 108) := quotient_degree half alpha p halpha hp col r
21:   have hkpow (n : Nat) : (κ^n).totalDegree ≤ n :=
22:     (totalDegree_pow _ _).trans (by nlinarith)
23:   have hw (r : Fin 108) :
24:       (κ*e 0 r+κ^2*e 1 r+κ^3*e 2 r).totalDegree ≤ 60 := by
25:     apply add_bound
26:     · exact add_bound ((mul_bound hk (he 0 r)).trans (by decide))
27:         ((mul_bound (hkpow 2) (he 1 r)).trans (by decide))
28:     · exact mul_bound (hkpow 3) (he 2 r)
29:   have hg (r : Fin 108) : (κ^2*e 1 r+κ^3*e 2 r).totalDegree ≤ 60 :=
30:     add_bound ((mul_bound (hkpow 2) (he 1 r)).trans (by decide))
31:       (mul_bound (hkpow 3) (he 2 r))
32:   unfold observation
33:   split_ifs
34:   · simp
35:   · apply totalDegree_finsetSum_le
36:     intro r _
37:     exact (mul_bound (hq r) (he row r)).trans (by decide)
38:   · exact poly_degree quarter _ _ 25 60 hq hw _
39:   · exact poly_degree quarter _ _ 25 60 hq hg _
40: 
41: theorem entry_degree [Nontrivial F] (half quarter : F) (i j : Fin 13) :
42:     (polyMinor half quarter i j).totalDegree ≤ 85 := by
43:   have hmul : ((X (12:Fin 36)*X 13 : Poly (F:=F))).totalDegree ≤ 2 := by
44:     simpa using totalDegree_mul (X (12:Fin 36) : Poly (F:=F)) (X 13)
45:   unfold polyMinor normalizedMinor minor
46:   apply observation_degree
47:   · exact add_bound (by simp) hmul
48:   · exact sub_bound hmul (by simp)
49:   · rw [totalDegree_neg]
50:     exact add_bound (by simp) (by simp)
51:   · simp
52:   · simp
53:   · intro r; simp
54:   · apply root_coefficients_degree
55:     intro r; simp
```

## Additional exact helper bodies — `crates/aspis-statement/src/pool_v1/pair_forest_copy_terminal.rs` (SHA256 7371e743a71357f259a58a20c7169188d5c3adb4010c13b6a792c6c65b8cb4a0)

### Lines 138–180
```text
138: pub(crate) struct Selectors {
139:     pub(crate) high: [QM31; 64],
140:     pub(crate) low: [QM31; 16],
141: }
142: 
143: impl Selectors {
144:     fn expand<const N: usize>(coordinates: &[QM31]) -> [QM31; N] {
145:         let mut weights = [QM31::ZERO; N];
146:         weights[0] = QM31::ONE;
147:         let mut len = 1usize;
148:         for coordinate in coordinates {
149:             let prepared = PreparedQm31Multiplier::new(*coordinate);
150:             for index in (0..len).rev() {
151:                 let parent = weights[index];
152:                 let right = prepared.mul(parent);
153:                 weights[2 * index] = parent.sub(right);
154:                 weights[2 * index + 1] = right;
155:             }
156:             len *= 2;
157:         }
158:         weights
159:     }
160: 
161:     pub(crate) fn at_point(point: &[QM31; 10]) -> Self {
162:         Self {
163:             high: Self::expand(&point[..6]),
164:             low: Self::expand(&point[6..]),
165:         }
166:     }
167: 
168:     #[inline(never)]
169:     pub(crate) fn boxed_at_point(point: &[QM31; 10]) -> Box<Self> {
170:         Box::new(Self::at_point(point))
171:     }
172: 
173:     #[inline(always)]
174:     pub(crate) fn row(&self, row: usize) -> QM31 {
175:         debug_assert!(row < POOL_V1_PAIR_FOREST_COPY_TERMINAL_ROWS_V1);
176:         self.high[row >> 4].mul(self.low[row & 15])
177:     }
178: 
179:     #[cfg(any(test, not(feature = "pool-v1-pair-forest-active-mask-basis-audit")))]
180:     fn active_literal(&self) -> QM31 {
```
## Additional exact helper bodies — `crates/aspis-core/src/state_only_hiding.rs` (SHA256 18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f)

### Lines 472–610
```text
472: fn state_only_shared_factor_powers(
473:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
474: ) -> [QM31; STATE_ONLY_HIDING_FACTOR_DEGREE + 1] {
475:     let linear = mask_linear(0, point);
476:     let mut powers = [QM31::ONE; STATE_ONLY_HIDING_FACTOR_DEGREE + 1];
477:     powers[1] = linear;
478:     for exponent in 2..=STATE_ONLY_HIDING_FACTOR_DEGREE {
479:         powers[exponent] = powers[exponent - 1].mul(linear);
480:     }
481:     powers
482: }
483: 
484: fn mask_linear(family: usize, point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> QM31 {
485:     point
486:         .iter()
487:         .enumerate()
488:         .fold(QM31::ZERO, |sum, (variable, value)| {
489:             let scalar = 3 + 22 * variable + family * (17 + 8 * variable);
490:             sum.add(value.mul_m31(M31(scalar as u32)))
491:         })
492: }
493: 
494: /// Evaluate the two linear forms used by the selected terminal from the same
495: /// add-only sufficient statistics. With `S0 = sum z_i` and
496: /// `S1 = sum i*z_i`, the frozen forms are exactly
497: /// `L0 = 3*S0 + 22*S1` and `L16 = 275*S0 + 150*S1`.
498: #[inline(always)]
499: fn selected_mask_linears(point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> (QM31, QM31) {
500:     let mut suffix = QM31::ZERO;
501:     let mut weighted = QM31::ZERO;
502:     for variable in (0..STATE_ONLY_HIDING_SUMCHECK_ROUNDS).rev() {
503:         suffix = suffix.add(point[variable]);
504:         if variable != 0 {
505:             weighted = weighted.add(suffix);
506:         }
507:     }
508:     (
509:         suffix.mul_m31(M31(3)).add(weighted.mul_m31(M31(22))),
510:         suffix.mul_m31(M31(275)).add(weighted.mul_m31(M31(150))),
511:     )
512: }
513: 
514: fn mask_power(value: QM31, exponent: usize) -> QM31 {
515:     (0..exponent).fold(QM31::ONE, |power, _| power.mul(value))
516: }
517: 
518: /// Exact fixed addition chain for the explicit degree-26 factor.
519: #[inline(always)]
520: fn mask_power_26(value: QM31) -> QM31 {
521:     let x2 = value.square();
522:     let x4 = x2.square();
523:     let x8 = x4.square();
524:     let x16 = x8.square();
525:     x16.mul(x8).mul(x2)
526: }
527: 
528: fn explicit_mask_factor(point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS]) -> QM31 {
529:     QM31::ONE.add(mask_power(
530:         mask_linear(EXPLICIT_FACTOR_FAMILY, point),
531:         EXPLICIT_FACTOR_EXPONENT,
532:     ))
533: }
534: 
535: pub fn state_only_mask_tower_basis(coordinate: usize) -> QM31 {
536:     match coordinate {
537:         0 => QM31::ONE,
538:         1 => QM31 {
539:             c0: CM31::new(M31::ZERO, M31::ONE),
540:             c1: CM31::ZERO,
541:         },
542:         2 => QM31 {
543:             c0: CM31::ZERO,
544:             c1: CM31::ONE,
545:         },
546:         3 => QM31 {
547:             c0: CM31::ZERO,
548:             c1: CM31::new(M31::ZERO, M31::ONE),
549:         },
550:         _ => panic!("state-only hiding tower coordinate out of range"),
551:     }
552: }
553: 
554: /// Public degree-26-or-less factors for the state-only masking candidate.
555: ///
556: /// The semantic and mask-only columns share one dense linear form and one
557: /// cached `L^0..L^26` table. Their disjoint even/odd exponent schedules expose
558: /// all 1080 terminal-quotient directions in the q29 rank gate. The explicit
559: /// QM31 mask deliberately keeps an independent `1 + L_16^26` factor; sharing
560: /// it drops the rank to 1076.
561: pub fn state_only_mask_factors(
562:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
563: ) -> StateOnlyMaskFactors {
564:     let powers = state_only_shared_factor_powers(point);
565:     let c1 = core::array::from_fn(|column| {
566:         let exponent = usize::from(FACTOR_EXPONENTS[column]);
567:         mul_tower_basis(powers[exponent], column & 3)
568:     });
569:     StateOnlyMaskFactors {
570:         c1,
571:         mask_only_c1: core::array::from_fn(|column| {
572:             mul_tower_basis(
573:                 powers[usize::from(MASK_ONLY_FACTOR_EXPONENTS[column])],
574:                 column & 3,
575:             )
576:         }),
577:         explicit_g: QM31::ONE
578:             .add(mask_linear(EXPLICIT_FACTOR_FAMILY, point).pow(EXPLICIT_FACTOR_EXPONENT as u64)),
579:     }
580: }
581: 
582: pub fn state_only_c1_mask_factor(
583:     column: usize,
584:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
585: ) -> QM31 {
586:     assert!(column < STATE_ONLY_HIDING_C1_COLUMNS);
587:     let family = usize::from(FACTOR_FAMILIES[column]);
588:     let exponent = usize::from(FACTOR_EXPONENTS[column]);
589:     state_only_mask_tower_basis(column & 3).mul(mask_power(mask_linear(family, point), exponent))
590: }
591: 
592: pub fn state_only_explicit_g_mask_factor(
593:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
594: ) -> QM31 {
595:     explicit_mask_factor(point)
596: }
597: 
598: /// Degree-at-most-26 factors for the ten selected full-domain M31 mask-only
599: /// columns. They use the rank-pinned unused odd powers of the same dense
600: /// linear form as the semantic columns, with distinct tower rotations.
601: pub fn state_only_mask_only_c1_factor(
602:     mask_column: usize,
603:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
604: ) -> QM31 {
605:     assert!(mask_column < STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS);
606:     let exponent = usize::from(MASK_ONLY_FACTOR_EXPONENTS[mask_column]);
607:     mul_tower_basis(mask_power(mask_linear(0, point), exponent), mask_column & 3)
608: }
609: 
610: /// Evaluate the exact degree-at-most-27 mask polynomial terminal from the 16
```
## Additional exact helper bodies — `crates/aspis-core/src/v6_transcript.rs` (SHA256 48275a37053ce5d33c7ec61caf6301863666f45a1e388c2c64bdb856708764cf)

### Lines 529–546
```text
529: pub fn v6_statement_points(z: &[QM31; V6_SEMANTIC_ROUNDS]) -> [[QM31; 10]; 3] {
530:     let mut successor = *z;
531:     let last = z.len() - 1;
532:     successor[last] = QM31::ONE.sub(z[last]);
533:     let mut carry = z[last];
534:     for coordinate in (0..last).rev() {
535:         let bit = z[coordinate];
536:         let bit_and_carry = bit.mul(carry);
537:         successor[coordinate] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
538:         carry = bit_and_carry;
539:     }
540:     let mut xor12 = *z;
541:     for coordinate in [7usize, 6] {
542:         xor12[coordinate] = QM31::ONE.sub(xor12[coordinate]);
543:     }
544:     [*z, successor, xor12]
545: }
546: 
```
## Additional exact helper bodies — `crates/aspis-statement/src/state_only_poseidon.rs` (SHA256 4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe)

### Lines 95–118
```text
95: pub fn successor_point(point: &[QM31; 10]) -> [QM31; 10] {
96:     let mut successor = *point;
97:     let mut carry = QM31::ONE;
98:     for coordinate in (0..point.len()).rev() {
99:         let bit = point[coordinate];
100:         let bit_and_carry = bit.mul(carry);
101:         successor[coordinate] = bit.add(carry).sub(bit_and_carry.add(bit_and_carry));
102:         carry = bit_and_carry;
103:     }
104:     successor
105: }
106: 
107: /// Toggle low row-index bits two and three.  On Boolean points this maps a
108: /// block's local row zero to local row twelve, where its absorption lives.
109: pub fn xor12_point(point: &[QM31; 10]) -> [QM31; 10] {
110:     let mut shifted = *point;
111:     for bit in [2usize, 3] {
112:         let coordinate = point.len() - 1 - bit;
113:         shifted[coordinate] = QM31::ONE.sub(shifted[coordinate]);
114:     }
115:     shifted
116: }
117: 
118: #[inline(always)]
```

### Lines 401–430
```text
401: fn leading_pair_packed(
402:     openings: &StateOnlyPoseidonOpenings,
403: ) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
404:     let mut state = openings.z;
405:     for lane in 0..RATE {
406:         state[lane] = state[lane].add(openings.xor12_z[lane]);
407:     }
408:     external_linear_lazy(&mut state);
409:     full_round_m31_constants_packed(
410:         full_round_m31_constants(state, EXTERNAL_INITIAL[0]),
411:         EXTERNAL_INITIAL[1],
412:     )
413: }
414: 
415: #[inline(always)]
416: fn interpolate_three_constant_limb(
417:     weight0: u32,
418:     weight1: u32,
419:     weight2: u32,
420:     constant0: u32,
421:     constant1: u32,
422:     constant2: u32,
423: ) -> M31 {
424:     M31::reduce_u64(
425:         u64::from(weight0) * u64::from(constant0)
426:             + u64::from(weight1) * u64::from(constant1)
427:             + u64::from(weight2) * u64::from(constant2),
428:     )
429: }
430: 
```

### Lines 484–585
```text
484: fn interpolated_full_pair(
485:     state: [QM31; POSEIDON2_WIDTH],
486:     local: &[QM31; 16],
487: ) -> [QM31; POSEIDON2_WIDTH] {
488:     let weights = [local[1], local[9], local[10]];
489:     let even = interpolate_three_constant_columns(
490:         weights,
491:         EXTERNAL_INITIAL[2],
492:         EXTERNAL_FINAL[0],
493:         EXTERNAL_FINAL[2],
494:     );
495:     let odd = interpolate_three_constant_columns(
496:         weights,
497:         EXTERNAL_INITIAL[3],
498:         EXTERNAL_FINAL[1],
499:         EXTERNAL_FINAL[3],
500:     );
501:     full_round(full_round(state, even), odd)
502: }
503: 
504: fn interpolated_full_pair_packed(
505:     state: [QM31; POSEIDON2_WIDTH],
506:     local: &[QM31; 16],
507: ) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
508:     let weights = [local[1], local[9], local[10]];
509:     let even = interpolate_three_constant_columns(
510:         weights,
511:         EXTERNAL_INITIAL[2],
512:         EXTERNAL_FINAL[0],
513:         EXTERNAL_FINAL[2],
514:     );
515:     let odd = interpolate_three_constant_columns(
516:         weights,
517:         EXTERNAL_INITIAL[3],
518:         EXTERNAL_FINAL[1],
519:         EXTERNAL_FINAL[3],
520:     );
521:     full_round_packed(full_round(state, even), odd)
522: }
523: 
524: fn interpolated_internal_pair(
525:     state: [QM31; POSEIDON2_WIDTH],
526:     local: &[QM31; 16],
527: ) -> [QM31; POSEIDON2_WIDTH] {
528:     const ROWS: [usize; 7] = [2, 3, 4, 5, 6, 7, 8];
529:     let weights = ROWS.map(|row| local[row]);
530:     let even_constants = ROWS.map(|row| M31(INTERNAL[2 * (row - 2)]));
531:     let odd_constants = ROWS.map(|row| M31(INTERNAL[2 * (row - 2) + 1]));
532:     let even = qm31_m31_dot(&weights, &even_constants);
533:     let odd = qm31_m31_dot(&weights, &odd_constants);
534:     internal_round(internal_round(state, even), odd)
535: }
536: 
537: /// Evaluate the four injectively packed successor-state constraints.
538: ///
539: /// On an active Boolean row the result is zero exactly when the state at
540: /// `succ(z)` is the output of the row's two pinned Poseidon rounds (including
541: /// row zero's absorption and leading external layer).  No intermediate-round
542: /// state is constrained or committed.
543: #[inline(never)]
544: pub fn evaluate_state_only_poseidon_oracle(
545:     openings: &StateOnlyPoseidonOpenings,
546:     selectors: &StateOnlyPoseidonSelectors,
547: ) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
548:     let leading_low = selectors.local[0];
549:     let full_low = [1usize, 9, 10]
550:         .into_iter()
551:         .fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
552:     let internal_low = (2usize..=8).fold(QM31::ZERO, |sum, row| sum.add(selectors.local[row]));
553:     let active_low = leading_low.add(full_low).add(internal_low);
554: 
555:     let leading = leading_pair(openings);
556:     let full = interpolated_full_pair(openings.z, &selectors.local);
557:     let internal = interpolated_internal_pair(openings.z, &selectors.local);
558:     let weights = [
559:         active_low,
560:         leading_low.neg(),
561:         full_low.neg(),
562:         internal_low.neg(),
563:     ];
564: 
565:     core::array::from_fn(|group| {
566:         let start = 4 * group;
567:         let target = qm31_pack_base4(&openings.succ_z[start..start + 4]);
568:         let leading = qm31_pack_base4(&leading[start..start + 4]);
569:         let full = qm31_pack_base4(&full[start..start + 4]);
570:         let internal = qm31_pack_base4(&internal[start..start + 4]);
571:         selectors.block.mul(qm31_sum_products4(
572:             [target, leading, full, internal],
573:             weights,
574:         ))
575:     })
576: }
577: 
578: /// Exact packed-projection implementation of [`evaluate_state_only_poseidon_oracle`].
579: ///
580: /// Only the two full/full branches benefit: their second external layer is
581: /// consumed through its four packed adjoint functionals.  The internal branch
582: /// remains on the original path because a generic adjoint there would replace
583: /// additions by sixteen extension-field products.
584: #[inline(never)]
585: pub fn evaluate_state_only_poseidon_oracle_projected(
```
## Additional exact helper bodies — `docs/research/v8-no-work-100-20260907/experiments/positive_transfer.rs` (SHA256 3a19043d2f40f168cb2127ba46e1795db7ea0751625c4fe48c73e02dab533cab)

### Lines 1–14
```text
1: //! Opt-in research design change: selected transfer output positivity.
2: //! No production feature enables this module. The legacy mask generator's
3: //! draw order is retained; its active-row1014/c3 draw is discarded before C1.
4: //! New transcript framing binds this adapter, not a claim of unchanged ZK.
5: use super::*;
6: use aspis_statement::pool_v1::*;
7: #[cfg(not(v8_performance_sbf))] use aspis_statement::StateOnlyTraceFoundation;
8: #[cfg(not(v8_performance_sbf))]
9: #[path="selected_transfer_zero.rs"] mod zero_fixture;
10: 
11: pub const ROW: usize = 1014;
12: pub const COL: usize = 3;
13: pub const LANE: usize = 94;
14: pub const PROFILE: &[u8] = b"AV8/positive-transfer/active-cell-overwrite/lane94/v1";
```

### Lines 72–96
```text
72: pub fn residual(claims:&[K;84])->K{
73:     claims[1].mul(claims[28+1]).mul(claims[COL]).sub(K::ONE)
74: }
75: pub fn selector(z:&[K;10])->K{
76:     z.iter().enumerate().fold(K::ONE,|a,(j,x)|a.mul(
77:         if (ROW>>(9-j))&1==1 {*x} else {K::ONE.sub(*x)}))
78: }
79: pub fn equality(z:&[K;10],zc:&[K;10])->K{
80:     z.iter().zip(zc).fold(K::ONE,|p,(a,b)|{
81:         let ab=a.mul(*b);p.mul(K::ONE.sub(*a).sub(*b).add(ab).add(ab))})
82: }
83: pub fn composition_delta(claims:&[K;84],z:&[K;10],theta:K)->K{
84:     // Source lane94 = packed group23, limb2; after four Poseidon lanes it
85:     // has theta exponent27. Do not treat extension-valued packing as casts.
86:     let weighted=selector(z).mul(residual(claims));
87:     let packed=corelib::field::qm31_pack_base4(&[K::ZERO,K::ZERO,weighted,K::ZERO]);
88:     let t2=theta.square();let t4=t2.square();let t8=t4.square();let t16=t8.square();
89:     t16.mul(t8).mul(t2).mul(theta).mul(packed)
90: }
91: pub fn terminal_delta(claims:&[K;84],z:&[K;10],theta:K,zc:&[K;10],eta:K)->K{
92:     eta.mul(equality(z,zc).mul(composition_delta(claims,z,theta)))
93: }
94: 
95: #[cfg(not(v8_performance_sbf))]
96: pub fn layout_control(){
```
