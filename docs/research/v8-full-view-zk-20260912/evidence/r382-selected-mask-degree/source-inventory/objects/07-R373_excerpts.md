# Exact numbered source excerpts

These excerpts preserve exact lines from the pinned copies listed in `inventory.json`; all line numbers are original source line numbers.

## performance_verifier.rs — SHA256 d6dad89eaa8d735f467055e96a8df12de7a391e2475ec26c44b2bc493624a62a — 9897 bytes

### lines 33-53
```rust
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
```

### lines 84-93
```rust
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
```

### lines 117-131
```rust
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
```

## positive_transfer.rs — SHA256 3a19043d2f40f168cb2127ba46e1795db7ea0751625c4fe48c73e02dab533cab — 6617 bytes

### lines 11-20
```rust
11: pub const ROW: usize = 1014;
12: pub const COL: usize = 3;
13: pub const LANE: usize = 94;
14: pub const PROFILE: &[u8] = b"AV8/positive-transfer/active-cell-overwrite/lane94/v1";
15: 
16: #[cfg(not(v8_performance_sbf))]
17: pub fn mask_cells() -> Vec<aspis_statement::TraceCell> {
18:     let mut cells=pool_v1_pair_forest_relation_free_mask_cells_v1().unwrap();
19:     assert_eq!(cells.len(),3803);
20:     assert_eq!(cells.iter().filter(|c|c.row as usize==ROW && c.column as usize==COL).count(),1);
```

### lines 72-98
```rust
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

## pair_forest_semantic_terminal.rs — SHA256 13b68f6db428268b2504068d79c88262e36d9abd22fb60e345612eff6e2cd90b — 67908 bytes

### lines 28-68
```rust
28: pub const POOL_V1_PAIR_FOREST_TERMINAL_ROWS_V1: usize = 1024;
29: pub const POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1: usize = 16;
30: pub const POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1: usize = 3;
31: pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1: usize =
32:     POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS + 2;
33: pub const POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1: usize =
34:     POOL_V1_PAIR_FOREST_TERMINAL_POINTS_V1 * POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1;
35: pub const POOL_V1_PAIR_FOREST_SOURCE_SEMANTIC_LANES_V1: usize = 94;
36: pub const POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1: usize = 24;
37: pub const POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1: usize = 4;
38: pub const POOL_V1_PAIR_FOREST_COPY_LANES_V1: usize = 1;
39: pub const POOL_V1_PAIR_FOREST_THETA_LANES_V1: usize = POOL_V1_PAIR_FOREST_POSEIDON_LANES_V1
40:     + POOL_V1_PAIR_FOREST_PACKED_SEMANTIC_LANES_V1
41:     + POOL_V1_PAIR_FOREST_COPY_LANES_V1;
42: pub const POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1: usize =
43:     POOL_V1_PAIR_FOREST_THETA_LANES_V1 - 1;
44: pub const POOL_V1_PAIR_FOREST_SEMANTIC_ORACLE_INDIVIDUAL_DEGREE_V1: usize = 26;
45: pub const POOL_V1_PAIR_FOREST_SEMANTIC_ZEROCHECK_INDIVIDUAL_DEGREE_V1: usize = 27;
46: pub const POOL_V1_PAIR_FOREST_MASKED_TERMINAL_DEGREE_V1: usize = 27;
47: pub const POOL_V1_PAIR_FOREST_TERMINAL_FIXED_HEAP_ALLOCATIONS_V1: usize =
48:     if cfg!(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit") {
49:         2
50:     } else {
51:         1
52:     };
53: pub const POOL_V1_PAIR_FOREST_TERMINAL_SELECTOR_HEAP_BYTES_V1: usize =
54:     core::mem::size_of::<Selectors>();
55: 
56: const SELECTED_H1_COLUMN: usize =
57:     POOL_V1_PAIR_FOREST_TERMINAL_C1_COLUMNS_V1 + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
58: const SELECTED_G_COLUMN: usize = SELECTED_H1_COLUMN + 1;
59: const VALUE_AUXILIARY_BLOCK: usize = 63;
60: const INPUT_OCCUPANCY_ROW: usize = 63 * 16 + 9;
61: const OUTPUT_OCCUPANCY_ROW: usize = 63 * 16 + 10;
62: 
63: const _: () = assert!(DIGEST_ELEMS == 8);
64: const _: () = assert!(POSEIDON2_WIDTH == 16);
65: const _: () = assert!(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1 == 28);
66: const _: () = assert!(POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_CLAIMS_V1 == 84);
67: const _: () = assert!(POOL_V1_PAIR_FOREST_THETA_LANES_V1 == 29);
68: const _: () = assert!(POOL_V1_PAIR_FOREST_THETA_COLLISION_DEGREE_V1 == 28);
```

### lines 106-124
```rust
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
```

### lines 211-215
```rust
211: fn poseidon_selectors(selectors: &Selectors) -> StateOnlyPoseidonSelectors {
212:     StateOnlyPoseidonSelectors {
213:         block: sum_high(selectors, &[0..57]),
214:         local: selectors.low,
215:     }
```

### lines 241-314
```rust
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
261:     let full_or_rate =
262:         PreparedQm31Multiplier::new(full_initial_selector.add(rate_initial_selector));
263:     let mut initial = core::array::from_fn(|lane| {
264:         if lane < RATE {
265:             full_or_rate.mul(openings.z[lane])
266:         } else {
267:             full.mul(openings.z[lane])
268:         }
269:     });
270:     let note_first = selectors.high[1]
271:         .add(selectors.high[30])
272:         .add(transfer_first);
273:     let domain = selectors.high[0]
274:         .mul_m31(DOMAIN_OWNER_KEY)
275:         .add(note_first.mul_m31(DOMAIN_NOTE))
276:         .add(selectors.high[25].mul_m31(DOMAIN_NULLIFIER));
277:     let length = selectors.high[0]
278:         .mul_m31(M31(8))
279:         .add(note_first.mul_m31(M31(18)))
280:         .add(selectors.high[25].mul_m31(M31(16)));
281:     initial[RATE] = initial[RATE].sub(selectors.low[0].mul(domain));
282:     initial[RATE + 1] = initial[RATE + 1].sub(selectors.low[0].mul(length));
283: 
284:     let mut chunk_eight = selectors.high[0]
285:         .add(selectors.high[1])
286:         .add(selectors.high[2])
287:         .add(selectors.high[25])
288:         .add(selectors.high[26])
289:         .add(selectors.high[30])
290:         .add(selectors.high[31]);
291:     let mut chunk_two = selectors.high[3].add(selectors.high[32]);
292:     chunk_eight = chunk_eight.add(private_chunk_eight);
293:     chunk_two = chunk_two.add(private_chunk_two);
294:     #[cfg(not(feature = "pool-v1-pair-forest-semantic-factor-audit"))]
295:     let absorption = absorption_lanes_literal(
296:         selectors.low[12],
297:         fixed,
298:         chunk_two,
299:         chunk_eight,
300:         nodes,
301:         &openings.z,
302:     );
303:     #[cfg(feature = "pool-v1-pair-forest-semantic-factor-audit")]
304:     let absorption = absorption_lanes_factored(
305:         selectors.low[12],
306:         fixed,
307:         chunk_two,
308:         chunk_eight,
309:         nodes,
310:         &openings.z,
311:     );
312:     (initial, absorption)
313: }
314: 
```

### lines 381-391
```rust
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
```

### lines 394-463
```rust
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
```

### lines 465-519
```rust
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
```

### lines 530-605
```rust
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
```

### lines 609-694
```rust
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
```

### lines 1021-1120
```rust
1021: #[cfg(any(
1022:     test,
1023:     feature = "pool-v1-pair-forest-packed-digest-selector-tensor-audit"
1024: ))]
1025: #[inline(never)]
1026: fn public_digest_packed_selector_tensor(
1027:     public: SemanticPublic<'_>,
1028:     openings: &StateOnlyPoseidonOpenings,
1029:     selectors: &Selectors,
1030: ) -> [QM31; DIGEST_ELEMS / 4] {
1031:     let mut local_sums = [[QM31::ZERO; DIGEST_ELEMS / 4]; 3];
1032:     let anchor = left_digest_packed_selector_tensor(
1033:         selectors.high[56],
1034:         openings.z,
1035:         public.anchor,
1036:     );
1037:     local_sums[1][0] = local_sums[1][0].add(anchor[0]);
1038:     local_sums[1][1] = local_sums[1][1].add(anchor[1]);
1039:     let nullifier = left_digest_packed_selector_tensor(
1040:         selectors.high[26],
1041:         openings.z,
1042:         public.nullifier,
1043:     );
1044:     local_sums[1][0] = local_sums[1][0].add(nullifier[0]);
1045:     local_sums[1][1] = local_sums[1][1].add(nullifier[1]);
1046:     let recipient = optional_recipient_packed_selector_tensor(
1047:         public.recipient,
1048:         openings.z,
1049:         selectors.high[29],
1050:     );
1051:     local_sums[1][0] = local_sums[1][0].add(recipient[0]);
1052:     local_sums[1][1] = local_sums[1][1].add(recipient[1]);
1053:     let change = left_digest_packed_selector_tensor(
1054:         selectors.high[32],
1055:         openings.z,
1056:         public.change,
1057:     );
1058:     local_sums[1][0] = local_sums[1][0].add(change[0]);
1059:     local_sums[1][1] = local_sums[1][1].add(change[1]);
1060: 
1061:     let source = public.transition.live_snapshot;
1062:     let after = public.transition.candidate_afterstate;
1063:     let next_pair_index = source.next_pair_index;
1064:     let source_frontier = source.frontier;
1065:     let opened_z = openings.z;
1066:     let selector_high = selectors.high;
1067:     let (append_local0, append_local12) = append_levels_packed_selector_tensor(
1068:         next_pair_index,
1069:         source_frontier,
1070:         opened_z,
1071:         selector_high,
1072:     );
1073:     local_sums[0][0] = local_sums[0][0].add(append_local0[0]);
1074:     local_sums[0][1] = local_sums[0][1].add(append_local0[1]);
1075:     local_sums[2][0] = local_sums[2][0].add(append_local12[0]);
1076:     local_sums[2][1] = local_sums[2][1].add(append_local12[1]);
1077:     let next_root = left_digest_packed_selector_tensor(
1078:         selector_high[53],
1079:         opened_z,
1080:         after.next_root,
1081:     );
1082:     local_sums[1][0] = local_sums[1][0].add(next_root[0]);
1083:     local_sums[1][1] = local_sums[1][1].add(next_root[1]);
1084:     let carry = core::cmp::min(next_pair_index.trailing_ones() as usize, 20);
1085:     let carry_index = core::cmp::min(carry, 19);
1086:     let carry_contribution = optional_carry_packed_selector_tensor(
1087:         carry,
1088:         opened_z,
1089:         selector_high[33 + carry_index],
1090:         after.next_frontier[carry_index],
1091:     );
1092:     local_sums[1][0] = local_sums[1][0].add(carry_contribution[0]);
1093:     local_sums[1][1] = local_sums[1][1].add(carry_contribution[1]);
1094: 
1095:     let mut output = [QM31::ZERO; DIGEST_ELEMS / 4];
1096:     let low0 = PreparedQm31Multiplier::new(selectors.low[0]);
1097:     output[0] = output[0].add(low0.mul(local_sums[0][0]));
1098:     output[1] = output[1].add(low0.mul(local_sums[0][1]));
1099:     let low11 = PreparedQm31Multiplier::new(selectors.low[11]);
1100:     output[0] = output[0].add(low11.mul(local_sums[1][0]));
1101:     output[1] = output[1].add(low11.mul(local_sums[1][1]));
1102:     let low12 = PreparedQm31Multiplier::new(selectors.low[12]);
1103:     output[0] = output[0].add(low12.mul(local_sums[2][0]));
1104:     output[1] = output[1].add(low12.mul(local_sums[2][1]));
1105:     output
1106: }
1107: 
1108: #[cfg(any(test, feature = "pool-v1-pair-forest-packed-digest-audit"))]
1109: #[inline(always)]
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
```

### lines 1122-1183
```rust
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
```

### lines 1185-1310
```rust
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
```

### lines 1312-1328
```rust
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
```

### lines 1396-1431
```rust
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
```

### lines 1969-1970
```rust
1969: #[path="r20_digest_factored.rs"]
1970: mod r20_digest_factored;
```

## pair_forest_copy_terminal.rs — SHA256 7371e743a71357f259a58a20c7169188d5c3adb4010c13b6a792c6c65b8cb4a0 — 70611 bytes

### lines 137-177
```rust
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
```

### lines 179-230
```rust
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
191:     }
192: 
193:     #[cfg(any(test, feature = "pool-v1-pair-forest-active-mask-basis-audit"))]
194:     fn active_mask_basis(&self) -> QM31 {
195:         const MASKS: [u16; 7] = [6144, 6145, 4097, 2048, 2049, 26214, 1749];
196:         let mut high_sums = [QM31::ZERO; MASKS.len()];
197:         let mut block = 0usize;
198:         while block < constants::ACTIVE_ROW_MASKS.len() {
199:             let mask = constants::ACTIVE_ROW_MASKS[block];
200:             let coordinate = match mask {
201:                 6144 => 0,
202:                 6145 => 1,
203:                 4097 => 2,
204:                 2048 => 3,
205:                 2049 => 4,
206:                 26214 => 5,
207:                 1749 => 6,
208:                 _ => unreachable!("generated Copy active mask outside frozen basis"),
209:             };
210:             high_sums[coordinate] = high_sums[coordinate].add(self.high[block]);
211:             block += 1;
212:         }
213:         let mut sum = QM31::ZERO;
214:         let mut coordinate = 0usize;
215:         while coordinate < MASKS.len() {
216:             sum = sum
217:                 .add(high_sums[coordinate].mul(selector_mask_sum_16(&self.low, MASKS[coordinate])));
218:             coordinate += 1;
219:         }
220:         sum
221:     }
222: 
223:     #[inline(always)]
224:     fn active(&self) -> QM31 {
225:         #[cfg(not(feature = "pool-v1-pair-forest-active-mask-basis-audit"))]
226:         return self.active_literal();
227:         #[cfg(feature = "pool-v1-pair-forest-active-mask-basis-audit")]
228:         return self.active_mask_basis();
229:     }
230: }
```

### lines 232-329
```rust
232: #[cfg(any(test, not(feature = "pool-v1-pair-forest-pattern-window-audit")))]
233: fn pattern_values_literal(
234:     openings: &[QM31; POSEIDON2_WIDTH],
235:     lambda: QM31,
236: ) -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
237:     let mut powers = [QM31::ZERO; POSEIDON2_WIDTH];
238:     let mut power = lambda;
239:     let mut limb = 0usize;
240:     while limb < POSEIDON2_WIDTH {
241:         powers[limb] = power;
242:         power = power.mul(lambda);
243:         limb += 1;
244:     }
245:     let mut result = [QM31::ZERO; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1];
246:     let mut pattern_index = 0usize;
247:     while pattern_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1 {
248:         let pattern = constants::COPY_PATTERNS[pattern_index];
249:         let mut value = QM31::ZERO;
250:         limb = 0;
251:         while limb < POSEIDON2_WIDTH {
252:             if pattern.kinds[limb] == 1 {
253:                 let source = openings[usize::from(pattern.columns[limb])]
254:                     .add(lift_m31(M31(pattern.offsets[limb])));
255:                 value = value.add(powers[limb].mul(source));
256:             }
257:             limb += 1;
258:         }
259:         result[pattern_index] = value;
260:         pattern_index += 1;
261:     }
262:     result
263: }
264: 
265: /// Exact CSE for the frozen fourteen-pattern table. Pattern 0 is the two
266: /// adjacent eight-limb windows, patterns 2 and 3 are exact six-limb prefixes,
267: /// and pattern 10 differs from pattern 13 only by its final public offset.
268: #[cfg(any(test, feature = "pool-v1-pair-forest-pattern-window-audit"))]
269: fn pattern_values_windowed(
270:     openings: &[QM31; POSEIDON2_WIDTH],
271:     lambda: QM31,
272: ) -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
273:     let mut powers = [QM31::ZERO; 8];
274:     let mut power = lambda;
275:     let mut slot = 0usize;
276:     while slot < powers.len() {
277:         powers[slot] = power;
278:         power = power.mul(lambda);
279:         slot += 1;
280:     }
281:     let prepared: [PreparedQm31Multiplier; 8] = powers.map(PreparedQm31Multiplier::new);
282:     let window = |start: usize| {
283:         let mut value = QM31::ZERO;
284:         let mut slot = 0usize;
285:         while slot < 8 {
286:             value = value.add(prepared[slot].mul(openings[start + slot]));
287:             slot += 1;
288:         }
289:         value
290:     };
291:     let window_0 = window(0);
292:     let window_1 = window(1);
293:     let window_2 = window(2);
294:     let window_8 = window(8);
295:     let mut result = [QM31::ZERO; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1];
296:     result[0] = window_0.add(prepared[7].mul(window_8));
297:     result[1] = window_0;
298:     result[2] = window_2
299:         .sub(prepared[6].mul(openings[8]))
300:         .sub(prepared[7].mul(openings[9]));
301:     result[3] = window_0
302:         .sub(prepared[6].mul(openings[6]))
303:         .sub(prepared[7].mul(openings[7]));
304:     result[4] = prepared[0]
305:         .mul(openings[0])
306:         .add(prepared[1].mul(openings[1]));
307:     result[5] = prepared[0]
308:         .mul(openings[6])
309:         .add(prepared[1].mul(openings[7]));
310:     result[6] = prepared[0].mul(openings[0]);
311:     result[7] = prepared[0].mul(openings[10]);
312:     result[8] = prepared[0].mul(openings[1]);
313:     result[9] = prepared[0].mul(openings[2]);
314:     result[10] = window_8.add(prepared[7].mul(lift_m31(M31(1_051_521_018))));
315:     result[11] = window_2;
316:     result[12] = window_1;
317:     result[13] = window_8;
318:     result
319: }
320: 
321: fn pattern_values(
322:     openings: &[QM31; POSEIDON2_WIDTH],
323:     lambda: QM31,
324: ) -> [QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1] {
325:     #[cfg(not(feature = "pool-v1-pair-forest-pattern-window-audit"))]
326:     return pattern_values_literal(openings, lambda);
327:     #[cfg(feature = "pool-v1-pair-forest-pattern-window-audit")]
328:     return pattern_values_windowed(openings, lambda);
329: }
```

### lines 331-377
```rust
331: #[derive(Clone, Copy)]
332: struct CopyRowExtension {
333:     producer_values: [QM31; 2],
334:     producer_weights: [QM31; 2],
335:     consumer_values: [QM31; 2],
336:     consumer_weights: [QM31; 2],
337: }
338: 
339: fn copy_residual(row: CopyRowExtension, helper: QM31, chi: QM31) -> QM31 {
340:     let denominators = [
341:         chi.sub(row.producer_values[0]),
342:         chi.sub(row.producer_values[1]),
343:         chi.sub(row.consumer_values[0]),
344:         chi.sub(row.consumer_values[1]),
345:     ];
346:     let producer_denominator = denominators[0].mul(denominators[1]);
347:     let consumer_denominator = denominators[2].mul(denominators[3]);
348:     let producer_numerator = row.producer_weights[0]
349:         .mul(denominators[1])
350:         .add(row.producer_weights[1].mul(denominators[0]));
351:     let consumer_numerator = row.consumer_weights[0]
352:         .mul(denominators[3])
353:         .add(row.consumer_weights[1].mul(denominators[2]));
354:     producer_denominator
355:         .mul(helper.mul(consumer_denominator).add(consumer_numerator))
356:         .sub(consumer_denominator.mul(producer_numerator))
357: }
358: 
359: #[inline(always)]
360: fn link_weight(
361:     link: CompiledPoolV1PairForestLink,
362:     append_index: u64,
363:     variant: PoolV1PairForestCompiledVariantV1,
364: ) -> M31 {
365:     match link.weight_kind {
366:         0 => M31::ONE,
367:         1 => M31(u32::from(
368:             variant == PoolV1PairForestCompiledVariantV1::PrivateTransfer,
369:         )),
370:         2 => M31(u32::from(
371:             variant == PoolV1PairForestCompiledVariantV1::Withdrawal,
372:         )),
373:         3 => M31(1 - ((append_index >> link.weight_level) & 1) as u32),
374:         4 => M31(((append_index >> link.weight_level) & 1) as u32),
375:         _ => unreachable!("generated Pool V1 pair-forest Copy weight"),
376:     }
377: }
```

### lines 812-839
```rust
812: fn accumulate_endpoint_selector_tensor_basis(
813:     scratch: &mut [QM31],
814:     side: usize,
815:     endpoint: CompiledPoolV1PairForestEndpoint,
816:     tag: u32,
817:     weight: M31,
818:     selectors: &Selectors,
819: ) {
820:     let group = side + usize::from(endpoint.slot);
821:     let row = usize::from(endpoint.row);
822:     let local = row & 15;
823:     let high = selectors.high[row >> 4];
824:     let group_local = usize::from(COPY_GROUP_LOCAL_COORDINATES[group][local]);
825:     #[cfg(not(feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
826:     {
827:         scratch[COPY_SELECTOR_TENSOR_TAG_OFFSET + group_local] =
828:             scratch[COPY_SELECTOR_TENSOR_TAG_OFFSET + group_local].add(high.mul_m31(M31(tag)));
829:     }
830:     #[cfg(feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")]
831:     let _ = tag;
832:     let weight_index = COPY_SELECTOR_TENSOR_WEIGHT_OFFSET + group_local;
833:     scratch[weight_index] =
834:         scratch[weight_index].add(selected_binary_weight(high, weight));
835:     let pattern_local =
836:         usize::from(COPY_PATTERN_LOCAL_COORDINATES[group][usize::from(endpoint.pattern)][local]);
837:     scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET + pattern_local] =
838:         scratch[COPY_SELECTOR_TENSOR_PATTERN_OFFSET + pattern_local].add(high);
839: }
```

### lines 842-889
```rust
842: fn finish_selector_tensor_basis(
843:     scratch: &[QM31],
844:     patterns: &[QM31; POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1],
845:     selectors: &Selectors,
846: ) -> ([QM31; 4], [QM31; 4]) {
847:     #[cfg(all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
848:     let mut shifted_patterns = *patterns;
849:     #[cfg(all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
850:     for pattern in &mut shifted_patterns { pattern.c0.a = pattern.c0.a.add(M31(R58_TAG_BASE)); }
851:     #[cfg(all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
852:     let patterns = &shifted_patterns;
853: 
854:     #[cfg(all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
855:     let mut r114_tags=vec![QM31::ZERO;30];
856:     #[cfg(all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
857:     r114_tags_into(&mut r114_tags,selectors);
858:     let r114_value=|coordinate:usize|{
859:         #[cfg(all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))] {r114_tags[coordinate]}
860:         #[cfg(not(all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit")))] {copy_tag_coordinate_value(scratch,coordinate,selectors)}
861:     };
862:     let mut values = [QM31::ZERO; 4];
863:     let mut weights = [QM31::ZERO; 4];
864:     #[cfg(not(feature = "pool-v1-pair-forest-copy-finish-dot-basis-audit"))]
865:     {
866:         let mut coordinate = 0usize;
867:         while coordinate < COPY_GROUP_LOCAL_COORDINATE_GROUPS.len() {
868:             let group = usize::from(COPY_GROUP_LOCAL_COORDINATE_GROUPS[coordinate]);
869:             let low = selectors.low[usize::from(COPY_GROUP_LOCAL_COORDINATE_LOCALS[coordinate])];
870:             let tag_value = r114_value(coordinate);
871:             values[group] = values[group].add(tag_value.mul(low));
872:             weights[group] = weights[group]
873:                 .add(scratch[COPY_SELECTOR_TENSOR_WEIGHT_OFFSET + coordinate].mul(low));
874:             coordinate += 1;
875:         }
876:     }
877:     #[cfg(feature = "pool-v1-pair-forest-copy-finish-dot-basis-audit")]
878:     {
879:         let mut group = 0usize;
880:         while group < values.len() {
881:             let end = COPY_GROUP_LOCAL_GROUP_OFFSETS[group + 1];
882:             let mut coordinate = COPY_GROUP_LOCAL_GROUP_OFFSETS[group];
883:             while coordinate < end {
884:                 let count = core::cmp::min(4, end - coordinate);
885:                 let tag_values: [QM31; 4] = core::array::from_fn(|index| {
886:                     if index < count {
887:                         r114_value(coordinate+index)
888:                     } else {
889:                         QM31::ZERO
```

### lines 931-1099
```rust
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
```

### lines 1722-1723
```rust
1722: #[cfg(all(feature = "pool-v1-pair-forest-copy-selector-tensor-basis-audit", feature = "pool-v1-pair-forest-copy-tag-dot-basis-audit"))]
1723: include!("r57_selector_gather.rs");
```

## state_only_poseidon.rs — SHA256 4467d15c9d473cbd42caf33f21aa0192bed007b58ccaa4a61cb5691532cab7fe — 46644 bytes

### lines 124-140
```rust
124: fn pow5(value: QM31) -> QM31 {
125:     let square = value.square();
126:     square.square().mul(value)
127: }
128: 
129: #[inline(always)]
130: fn extension_limbs(value: QM31) -> [u32; 4] {
131:     [value.c0.a.0, value.c0.b.0, value.c1.a.0, value.c1.b.0]
132: }
133: 
134: #[inline(always)]
135: fn extension_from_raw_limbs(limbs: [u64; 4]) -> QM31 {
136:     QM31 {
137:         c0: CM31::new(M31::reduce_u62(limbs[0]), M31::reduce_u62(limbs[1])),
138:         c1: CM31::new(M31::reduce_u62(limbs[2]), M31::reduce_u62(limbs[3])),
139:     }
140: }
```

### lines 144-180
```rust
144: fn external_linear_lazy(state: &mut [QM31; POSEIDON2_WIDTH]) {
145:     let mut group = 0usize;
146:     while group < 4 {
147:         let start = 4 * group;
148:         let input = [
149:             state[start],
150:             state[start + 1],
151:             state[start + 2],
152:             state[start + 3],
153:         ];
154:         let input = input.map(extension_limbs);
155:         let mut output = 0usize;
156:         while output < 4 {
157:             let raw = core::array::from_fn(|limb| {
158:                 let a = u64::from(input[0][limb]);
159:                 let b = u64::from(input[1][limb]);
160:                 let c = u64::from(input[2][limb]);
161:                 let d = u64::from(input[3][limb]);
162:                 match output {
163:                     0 => 2 * a + 3 * b + c + d,
164:                     1 => a + 2 * b + 3 * c + d,
165:                     2 => a + b + 2 * c + 3 * d,
166:                     3 => 3 * a + b + c + 2 * d,
167:                     _ => unreachable!(),
168:                 }
169:             });
170:             state[start + output] = extension_from_raw_limbs(raw);
171:             output += 1;
172:         }
173:         group += 1;
174:     }
175:     let sums: [[u64; 4]; 4] = core::array::from_fn(|column| {
176:         core::array::from_fn(|limb| {
177:             u64::from(extension_limbs(state[column])[limb])
178:                 + u64::from(extension_limbs(state[4 + column])[limb])
179:                 + u64::from(extension_limbs(state[8 + column])[limb])
180:                 + u64::from(extension_limbs(state[12 + column])[limb])
```

### lines 332-413
```rust
332: fn full_round(
333:     mut state: [QM31; POSEIDON2_WIDTH],
334:     constants: [QM31; POSEIDON2_WIDTH],
335: ) -> [QM31; POSEIDON2_WIDTH] {
336:     for lane in 0..POSEIDON2_WIDTH {
337:         state[lane] = pow5(state[lane].add(constants[lane]));
338:     }
339:     external_linear_lazy(&mut state);
340:     state
341: }
342: 
343: /// Full round whose constants are pinned base-field values. Only c0.a changes
344: /// during the addition, avoiding three zero-limb additions per lane in the
345: /// two fixed leading rounds.
346: #[inline(never)]
347: fn full_round_m31_constants(
348:     mut state: [QM31; POSEIDON2_WIDTH],
349:     constants: [u32; POSEIDON2_WIDTH],
350: ) -> [QM31; POSEIDON2_WIDTH] {
351:     for lane in 0..POSEIDON2_WIDTH {
352:         state[lane].c0.a = state[lane].c0.a.add(M31(constants[lane]));
353:         state[lane] = pow5(state[lane]);
354:     }
355:     external_linear_lazy(&mut state);
356:     state
357: }
358: 
359: #[inline(never)]
360: fn full_round_packed(
361:     mut state: [QM31; POSEIDON2_WIDTH],
362:     constants: [QM31; POSEIDON2_WIDTH],
363: ) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
364:     for lane in 0..POSEIDON2_WIDTH {
365:         state[lane] = pow5(state[lane].add(constants[lane]));
366:     }
367:     external_linear_packed(state)
368: }
369: 
370: #[inline(never)]
371: fn full_round_m31_constants_packed(
372:     mut state: [QM31; POSEIDON2_WIDTH],
373:     constants: [u32; POSEIDON2_WIDTH],
374: ) -> [QM31; STATE_ONLY_POSEIDON_PACKED_LANES] {
375:     for lane in 0..POSEIDON2_WIDTH {
376:         state[lane].c0.a = state[lane].c0.a.add(M31(constants[lane]));
377:         state[lane] = pow5(state[lane]);
378:     }
379:     external_linear_packed(state)
380: }
381: 
382: #[inline(never)]
383: fn internal_round(mut state: [QM31; POSEIDON2_WIDTH], constant: QM31) -> [QM31; 16] {
384:     state[0] = pow5(state[0].add(constant));
385:     internal_linear_lazy(&mut state);
386:     state
387: }
388: 
389: fn leading_pair(openings: &StateOnlyPoseidonOpenings) -> [QM31; POSEIDON2_WIDTH] {
390:     let mut state = openings.z;
391:     for lane in 0..RATE {
392:         state[lane] = state[lane].add(openings.xor12_z[lane]);
393:     }
394:     external_linear_lazy(&mut state);
395:     full_round_m31_constants(
396:         full_round_m31_constants(state, EXTERNAL_INITIAL[0]),
397:         EXTERNAL_INITIAL[1],
398:     )
399: }
400: 
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
```

### lines 484-535
```rust
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
```

### lines 537-617
```rust
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
```

## state_only_hiding.rs — SHA256 18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f — 49493 bytes

### lines 12-30
```rust
12: pub const STATE_ONLY_HIDING_C1_COLUMNS: usize = 16;
13: pub const STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS: usize = 10;
14: /// Frozen production width until the selected hiding profile is integrated
15: /// across prefix/query/relation/terminal together.
16: pub const STATE_ONLY_HIDING_TOTAL_C1_COLUMNS: usize = STATE_ONLY_HIDING_C1_COLUMNS;
17: pub const STATE_ONLY_HIDING_C2_COLUMNS: usize = 2;
18: pub const STATE_ONLY_HIDING_TOTAL_GENERATOR_WIDTH: usize =
19:     STATE_ONLY_HIDING_TOTAL_C1_COLUMNS + STATE_ONLY_HIDING_C2_COLUMNS;
20: pub const STATE_ONLY_HIDING_SELECTED_TOTAL_C1_COLUMNS: usize =
21:     STATE_ONLY_HIDING_C1_COLUMNS + STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS;
22: pub const STATE_ONLY_HIDING_SELECTED_TOTAL_GENERATOR_WIDTH: usize =
23:     STATE_ONLY_HIDING_SELECTED_TOTAL_C1_COLUMNS + STATE_ONLY_HIDING_C2_COLUMNS;
24: pub const STATE_ONLY_HIDING_SEMANTIC_C1_START: usize = 0;
25: pub const STATE_ONLY_HIDING_MASK_ONLY_C1_START: usize = STATE_ONLY_HIDING_C1_COLUMNS;
26: pub const STATE_ONLY_HIDING_H1_GENERATOR_INDEX: usize = STATE_ONLY_HIDING_SELECTED_TOTAL_C1_COLUMNS;
27: pub const STATE_ONLY_HIDING_G_GENERATOR_INDEX: usize = STATE_ONLY_HIDING_H1_GENERATOR_INDEX + 1;
28: pub const STATE_ONLY_HIDING_SUMCHECK_ROUNDS: usize = 10;
29: pub const STATE_ONLY_HIDING_FACTOR_DEGREE: usize = 26;
30: pub const STATE_ONLY_HIDING_MASKED_ORACLE_DEGREE: usize = 27;
```

### lines 472-512
```rust
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
```

### lines 514-533
```rust
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
```

### lines 561-580
```rust
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
```

### lines 592-595
```rust
592: pub fn state_only_explicit_g_mask_factor(
593:     point: &[QM31; STATE_ONLY_HIDING_SUMCHECK_ROUNDS],
594: ) -> QM31 {
595:     explicit_mask_factor(point)
```

### lines 634-675
```rust
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
666:     for exponent in (0..STATE_ONLY_HIDING_FACTOR_DEGREE).rev() {
667:         shared = prepared_linear.mul(shared).add(coefficients[exponent]);
668:     }
669: 
670:     shared.add(
671:         QM31::ONE
672:             .add(mask_power_26(explicit_linear))
673:             .mul(explicit_g),
674:     )
675: }
```

## aspis-statement-Cargo.toml — SHA256 cf8babeac16a1987ed1dbd05454f77cb0f217779c33d6384a986eccf9e5b5231 — 3494 bytes

### lines 8-63
```rust
8: [features]
9: # Exposes the deliberately broken lambda^0 tagged-tuple compression solely
10: # for adversarial teeth/evaluation builds. The verifier program does not
11: # forward this feature; enabling it requires an explicit dependency feature.
12: insecure-test-logup-compression = []
13: # Derive only the public RATE512 circle/line coordinates touched by Spend
14: # queries. This preserves the proof and verifier equations while allowing a
15: # deployment build to dead-strip the six complete RATE512 lookup tables.
16: spend-dynamic-rate512 = []
17: # Host by default; the separate Pool V1 program enables this explicitly for
18: # SBF. Frozen verifier builds do not enable it.
19: pool-v1-kernel = []
20: # Audit-only algebraic rewrite for the pair-forest public-digest constraints.
21: # It packs each four-lane residual before applying its common selector; the
22: # default and released terminal retain the literal lane-by-lane evaluator.
23: pool-v1-pair-forest-packed-digest-audit = []
24: # Audit-only selector-tensor continuation of packed digest binding. Each
25: # binding keeps its two packed residuals, while `high[block] * low[local]` is
26: # contracted as three exact local-coordinate sums.
27: pool-v1-pair-forest-packed-digest-selector-tensor-audit = [
28:     "pool-v1-pair-forest-packed-digest-audit",
29: ]
30: # Audit-only exact `{0,1}` specialization for generated pair-forest Copy
31: # weights. The literal QM31-by-M31 multiplication remains the default.
32: pool-v1-pair-forest-binary-copy-weights-audit = []
33: # Audit-only memoization of generated Copy endpoint row selectors. The cache
34: # never supplies a value unless its stored row tag matches exactly.
35: pool-v1-pair-forest-endpoint-selector-cache-audit = []
36: # Audit-only exact common-factor extraction in the selected semantic lanes.
37: # It preserves all 94 source residuals and their 24 packed theta lanes.
38: pool-v1-pair-forest-semantic-factor-audit = []
39: # Audit-only exact CSE for the fourteen generated Copy tuple patterns.
40: pool-v1-pair-forest-pattern-window-audit = []
41: # Audit-only exact change of basis for the compiled Copy values.  Endpoint
42: # selectors are accumulated by their fixed tuple-pattern coordinate before
43: # the dynamic pattern values are multiplied, replacing 272 repeated QM31
44: # products by the 26 nonzero coordinates of the frozen four-by-fourteen
45: # support matrix.  Tags remain included through exact M31 multiplication.
46: pool-v1-pair-forest-copy-pattern-basis-audit = []
47: pool-v1-pair-forest-packed-range-audit = []
48: pool-v1-pair-forest-active-mask-basis-audit = []
49: pool-v1-pair-forest-copy-selector-tensor-basis-audit = [
50:     "pool-v1-pair-forest-copy-pattern-basis-audit",
51: ]
52: # Audit-only lazy-reduction dot kernel for the generated Copy tags. Endpoint
53: # products are regrouped by the exact `(side, slot, local)` tensor coordinate
54: # and reduced in batches of at most four M31 products.
55: pool-v1-pair-forest-copy-tag-dot-basis-audit = [
56:     "pool-v1-pair-forest-copy-selector-tensor-basis-audit",
57: ]
58: # Audit-only four-product contraction of the tag/low and weight/low tensor
59: # coordinates after exact endpoint collection.
60: pool-v1-pair-forest-copy-finish-dot-basis-audit = [
61:     "pool-v1-pair-forest-copy-selector-tensor-basis-audit",
62: ]
63: 
```

## r20_digest_factored.rs — SHA256 4691528b9c577d9fcbf8bdbd24f47675cac22d507de1c53bebe1836214e4c556 — 3864 bytes

### lines 1-99
```rust
1: //! Staged-only semantic digest candidate.
2: //!
3: //! This file is injected into the semantic-terminal module by an experiment
4: //! harness. It deliberately does not alter the production implementation.
5: //! The event rows, branch conditions, expected digests, and Merkle tweak are
6: //! copied from `public_digest_packed_selector_tensor`.
7: 
8: use super::*;
9: 
10: #[inline(never)]
11: pub(super) fn public_digest_packed_selector_tensor_r20(
12:     public: SemanticPublic<'_>,
13:     openings: &StateOnlyPoseidonOpenings,
14:     selectors: &Selectors,
15: ) -> [QM31; DIGEST_ELEMS / 4] {
16:     let mut hsum = [QM31::ZERO; 3];
17:     let mut expected_sum = [[QM31::ZERO; DIGEST_ELEMS / 4]; 3];
18: 
19:     // Record one source event into its destination local. The expected digest
20:     // is packed from canonical M31 limbs before applying the selector.
21:     let mut record = |group: usize, high: QM31, expected: &Digest, right_tweak: bool| {
22:         hsum[group] = hsum[group].add(high);
23:         for packed_group in 0..DIGEST_ELEMS / 4 {
24:             let start = 4 * packed_group;
25:             let limbs: [QM31; 4] = core::array::from_fn(|slot| {
26:                 let lane = start + slot;
27:                 let mut value = expected[lane];
28:                 if right_tweak && lane + 1 == DIGEST_ELEMS {
29:                     value = value.add(MERKLE_NODE_COMPRESSION_V3_TWEAK);
30:                 }
31:                 lift_m31(value)
32:             });
33:             expected_sum[group][packed_group] =
34:                 expected_sum[group][packed_group].add(high.mul(qm31_pack_base4(&limbs)));
35:         }
36:     };
37: 
38:     // Fixed digest events: local 11 / group 1.
39:     record(1, selectors.high[56], &public.anchor, false);
40:     record(1, selectors.high[26], &public.nullifier, false);
41:     if let Some(recipient) = public.recipient {
42:         record(1, selectors.high[29], &recipient, false);
43:     }
44:     record(1, selectors.high[32], &public.change, false);
45: 
46:     // Append levels: local 0 for empty-root branches, local 12 for frontier
47:     // branches. The empty-root branch retains the exact right-side tweak.
48:     let source = public.transition.live_snapshot;
49:     let after = public.transition.candidate_afterstate;
50:     let next_pair_index = source.next_pair_index;
51:     for level in 0..20 {
52:         let high = selectors.high[34 + level];
53:         if ((next_pair_index >> level) & 1) == 0 {
54:             record(0, high, &empty_root(level), true);
55:         } else {
56:             record(2, high, &source.frontier[level], false);
57:         }
58:     }
59: 
60:     record(1, selectors.high[53], &after.next_root, false);
61:     let carry = core::cmp::min(next_pair_index.trailing_ones() as usize, 20);
62:     if carry < 20 {
63:         record(
64:             1,
65:             selectors.high[33 + carry],
66:             &after.next_frontier[carry],
67:             false,
68:         );
69:     }
70: 
71:     let opened_group = |start: usize| -> [QM31; DIGEST_ELEMS / 4] {
72:         core::array::from_fn(|packed_group| {
73:             let limbs: [QM31; 4] =
74:                 core::array::from_fn(|slot| openings.z[start + 4 * packed_group + slot]);
75:             qm31_pack_base4(&limbs)
76:         })
77:     };
78:     let opened0 = opened_group(RATE);
79:     let opened1 = opened_group(0);
80:     let opened2 = opened1;
81:     let opened = [opened0, opened1, opened2];
82: 
83:     let mut output = [QM31::ZERO; DIGEST_ELEMS / 4];
84:     let low0 = PreparedQm31Multiplier::new(selectors.low[0]);
85:     let low11 = PreparedQm31Multiplier::new(selectors.low[11]);
86:     let low12 = PreparedQm31Multiplier::new(selectors.low[12]);
87:     let lows = [low0, low11, low12];
88:     for group in 0..3 {
89:         for packed_group in 0..DIGEST_ELEMS / 4 {
90:             let residual = lows[group].mul(
91:                 hsum[group]
92:                     .mul(opened[group][packed_group])
93:                     .sub(expected_sum[group][packed_group]),
94:             );
95:             output[packed_group] = output[packed_group].add(residual);
96:         }
97:     }
98:     output
99: }
```

## r57_selector_gather.rs — SHA256 6ad2756dff971727facbdc47a52161052d146460bcd3a34836e7c8583d674646 — 6663 bytes

### lines 1-45
```rust
1: // Included only in the selected tensor/tag profile. Derive all terms from
2: // the unchanged endpoint registry; no hand-maintained replacement schedule.
3: #[derive(Clone,Copy)]
4: struct R57Term { high:u8, kind:u8, level:u8 }
5: const fn r57_table()->([u16;74],[R57Term;544]) {
6:     let mut offsets=[0u16;74];
7:     let mut terms=[R57Term{high:0,kind:0,level:0};544];
8:     let mut next=0usize;let mut coordinate=0usize;
9:     while coordinate<73 {
10:         let mut index=0usize;
11:         while index<constants::COPY_LINKS.len() {
12:             let link=constants::COPY_LINKS[index];let mut side=0usize;
13:             while side<2 {
14:                 let ep=if side==0{link.producer}else{link.consumer};
15:                 let group=2*side+ep.slot as usize;let local=ep.row as usize&15;
16:                 let target=if coordinate<30{COPY_GROUP_LOCAL_COORDINATES[group][local]as usize}
17:                     else{30+COPY_PATTERN_LOCAL_COORDINATES[group][ep.pattern as usize][local]as usize};
18:                 if target==coordinate {
19:                     assert!(next<544 && ep.row<1024 && link.weight_kind<=4 && link.weight_level<64);
20:                     terms[next]=R57Term{high:(ep.row>>4)as u8,
21:                         kind:if coordinate<30{link.weight_kind}else{0},level:link.weight_level};
22:                     next+=1;
23:                 }
24:                 side+=1;
25:             }
26:             index+=1;
27:         }
28:         offsets[coordinate+1]=next as u16;coordinate+=1;
29:     }
30:     assert!(next==544);
31:     (offsets,terms)
32: }
33: static R57_TABLE:([u16;74],[R57Term;544])=r57_table();
34: 
35: #[inline(always)]
36: fn r57_enabled(term:R57Term,append:u64,variant:PoolV1PairForestCompiledVariantV1)->bool {
37:     match term.kind {
38:         0=>true,
39:         1=>variant==PoolV1PairForestCompiledVariantV1::PrivateTransfer,
40:         2=>variant==PoolV1PairForestCompiledVariantV1::Withdrawal,
41:         3=>((append>>term.level)&1)==0,
42:         4=>((append>>term.level)&1)==1,
43:         _=>unreachable!("source-generated Copy weight kind"),
44:     }
45: }
```

### lines 48-60
```rust
48: fn r113_retained_gather(scratch:&mut[QM31],selectors:&Selectors,append:u64,variant:PoolV1PairForestCompiledVariantV1){
49:     for coordinate in 0..73 {
50:         let mut raw=[0u64;4];
51:         let mut index=usize::from(R57_TABLE.0[coordinate]);
52:         let end=usize::from(R57_TABLE.0[coordinate+1]);
53:         while index<end {
54:             let term=R57_TABLE.1[index];
55:             if r57_enabled(term,append,variant) {
56:                 let value=selectors.high[usize::from(term.high)];
57:                 // At most 272 terms in a slot; each limb is at most u32::MAX.
58:                 // Therefore no u64 overflow, even before canonicality is used.
59:                 raw[0]=raw[0].wrapping_add(u64::from(value.c0.a.0));
60:                 raw[1]=raw[1].wrapping_add(u64::from(value.c0.b.0));
```

### lines 126-126
```rust
126: include!("r113_gather.rs");
```

## r113_gather.rs — SHA256 97cdf2ceb3b8a2135006462efffe9f984f0126d0094ee5eb5df22511c16c732d — 57288 bytes

### lines 1-18
```rust
1: // Generated from the pinned registry; exact integer expansion checked.
2: // Every positive intermediate has <=272 u32 terms, hence <2^41.
3: #[inline(never)]
4: fn r113_limb<const L:usize>(scratch:&mut[QM31],selectors:&Selectors,append:u64,variant:PoolV1PairForestCompiledVariantV1){
5:     assert!(scratch.len()>=103 && L<4);
6:     let v0=u64::from(if L==0{selectors.high[0].c0.a.0}else if L==1{selectors.high[0].c0.b.0}else if L==2{selectors.high[0].c1.a.0}else{selectors.high[0].c1.b.0});
7:     let v1=u64::from(if L==0{selectors.high[1].c0.a.0}else if L==1{selectors.high[1].c0.b.0}else if L==2{selectors.high[1].c1.a.0}else{selectors.high[1].c1.b.0});
8:     let v2=u64::from(if L==0{selectors.high[2].c0.a.0}else if L==1{selectors.high[2].c0.b.0}else if L==2{selectors.high[2].c1.a.0}else{selectors.high[2].c1.b.0});
9:     let v3=u64::from(if L==0{selectors.high[3].c0.a.0}else if L==1{selectors.high[3].c0.b.0}else if L==2{selectors.high[3].c1.a.0}else{selectors.high[3].c1.b.0});
10:     let v4=u64::from(if L==0{selectors.high[4].c0.a.0}else if L==1{selectors.high[4].c0.b.0}else if L==2{selectors.high[4].c1.a.0}else{selectors.high[4].c1.b.0});
11:     let v5=u64::from(if L==0{selectors.high[5].c0.a.0}else if L==1{selectors.high[5].c0.b.0}else if L==2{selectors.high[5].c1.a.0}else{selectors.high[5].c1.b.0});
12:     let v6=u64::from(if L==0{selectors.high[6].c0.a.0}else if L==1{selectors.high[6].c0.b.0}else if L==2{selectors.high[6].c1.a.0}else{selectors.high[6].c1.b.0});
13:     let v7=u64::from(if L==0{selectors.high[7].c0.a.0}else if L==1{selectors.high[7].c0.b.0}else if L==2{selectors.high[7].c1.a.0}else{selectors.high[7].c1.b.0});
14:     let v8=u64::from(if L==0{selectors.high[8].c0.a.0}else if L==1{selectors.high[8].c0.b.0}else if L==2{selectors.high[8].c1.a.0}else{selectors.high[8].c1.b.0});
15:     let v9=u64::from(if L==0{selectors.high[9].c0.a.0}else if L==1{selectors.high[9].c0.b.0}else if L==2{selectors.high[9].c1.a.0}else{selectors.high[9].c1.b.0});
16:     let v10=u64::from(if L==0{selectors.high[10].c0.a.0}else if L==1{selectors.high[10].c0.b.0}else if L==2{selectors.high[10].c1.a.0}else{selectors.high[10].c1.b.0});
17:     let v11=u64::from(if L==0{selectors.high[11].c0.a.0}else if L==1{selectors.high[11].c0.b.0}else if L==2{selectors.high[11].c1.a.0}else{selectors.high[11].c1.b.0});
18:     let v12=u64::from(if L==0{selectors.high[12].c0.a.0}else if L==1{selectors.high[12].c0.b.0}else if L==2{selectors.high[12].c1.a.0}else{selectors.high[12].c1.b.0});
```

### lines 360-368
```rust
360:     if L==0{scratch[101].c0.a=value;}else if L==1{scratch[101].c0.b=value;}else if L==2{scratch[101].c1.a=value;}else{scratch[101].c1.b=value;}
361:     let value=M31::reduce_u64(v150);
362:     if L==0{scratch[102].c0.a=value;}else if L==1{scratch[102].c0.b=value;}else if L==2{scratch[102].c1.a=value;}else{scratch[102].c1.b=value;}
363: }
364: #[inline(never)]
365: fn r57_gather(scratch:&mut[QM31],selectors:&Selectors,append:u64,variant:PoolV1PairForestCompiledVariantV1){
366:     r113_limb::<0>(scratch,selectors,append,variant);r113_limb::<1>(scratch,selectors,append,variant);
367:     r113_limb::<2>(scratch,selectors,append,variant);r113_limb::<3>(scratch,selectors,append,variant);
368: }
```


## Additional selected mask schedule constants

Source: `crates/aspis-core/src/state_only_hiding.rs`, SHA256 `18058112db3108a18f9d11f8d9ffb6f9c1b310b90b333010fd0f98cac480237f`.

```rust
391: const FACTOR_FAMILIES: [u8; STATE_ONLY_HIDING_C1_COLUMNS] = [0; 16];
392: const FACTOR_EXPONENTS: [u8; STATE_ONLY_HIDING_C1_COLUMNS] =
393:     [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 13, 25];
394: const MASK_ONLY_FACTOR_EXPONENTS: [u8; STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS] =
395:     [1, 3, 5, 7, 9, 11, 15, 17, 19, 21];
396: const EXPLICIT_FACTOR_EXPONENT: usize = STATE_ONLY_HIDING_FACTOR_DEGREE;
397: const EXPLICIT_FACTOR_FAMILY: usize = 16;
```
