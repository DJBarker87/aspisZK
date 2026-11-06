# NKQ source occurrence inventory

Status: inventory only; no native cut or root closure inferred from CLOSED child labels. Conservative alternative matches are retained pending typed resolution. Loops in callees require their admitted induction packets; no parent loop is unfolded. Each repeated validated_record/decode/mark call remains a distinct occurrence.

## TX1:136 verify_finish

Frozen source `crates/aspis-r1-cost-probe/src/r1_semantic.rs`:232, function text SHA256 `e35ca50a3b472d40538941b6c5eb2a28e31ab0143966925a99a1a851572495c7`. Source order below includes std calls and cfg(prover) exclusions; native cuts not yet established.

| Line | Occurrence text | Cover / required frame |
|---|---|---|
| 234 | `let (running, alpha, mut transcript) = semantic_rounds(&prefix, transcript)?;` | TX1:134 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 236 | `let (running, alpha, mut transcript, round_checks) = semantic_rounds(&prefix, transcript)?;` | cfg(prover), excluded by deployed feature parity; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 237 | `mark(obs, 2);` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 238 | `let claims = claims(&prefix)?;` | TX1:129 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 248 | `.terminal_qm31(&claims, &alpha, &original_challenges)` | TX1:256 OPEN; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 249 | `.map_err(¦_¦ Error::Public)?;` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 250 | `mark(obs, 3);` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 251 | `let mask = aspis_core::state_only_hiding::state_only_selected_mask_value(` | TX1:076 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 252 | `&core::array::from_fn(¦i¦ claims[0][i]),` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 253 | `&core::array::from_fn(¦i¦ claims[0][16 + i]),` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 257 | `let extra = prefix.validated_record(25)?.decode_k::<29>(87)?;` | TX1:141 CLOSED, TX1:147 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 258 | `let masked_terminal = mask.add(challenges.eta.mul(terminal)).add(extra[28]);` | TX1:001 CLOSED, TX1:007 CLOSED, TX1:013 CLOSED, TX1:017 CLOSED, TX1:024 CLOSED, TX1:029 CLOSED, TX1:047 CLOSED, TX1:051 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 260 | `return Err(Error::Terminal);` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 262 | `mark(obs, 4);` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 263 | `let state_before_z0 = transcript.state();` | TX1:146 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 264 | `let z0 = transcript.circle_validated(prefix.validated_record(25)?)?;` | TX1:141 CLOSED, TX1:142 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 265 | `let before_z1 = prefix.validated_record(26)?.decode_k::<29>(0)?;` | TX1:141 CLOSED, TX1:147 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 266 | `let z1 = transcript.circle_validated(prefix.validated_record(26)?)?;` | TX1:141 CLOSED, TX1:142 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 267 | `mark(obs, 5);` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 270 | `for (i, x) in [z0.x, z0.y, z1.x, z1.y].into_iter().enumerate() {` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 271 | `crate::trace::value(3, i, aspis_core::field::WideExact::from_qm31(x));` | cfg(prover), excluded by deployed feature parity; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 273 | `for (i, x) in challenges.with_alphas(&alpha).into_iter().enumerate() {` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 274 | `crate::trace::value(0, i, x);` | cfg(prover), excluded by deployed feature parity; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 276 | `for (i, row) in round_checks.iter().enumerate() {` | cfg(prover), excluded by deployed feature parity; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 277 | `for (j, x) in row.iter().enumerate() {` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 278 | `crate::trace::value(1, 3 * i + j, aspis_core::field::WideExact::from_qm31(*x));` | cfg(prover), excluded by deployed feature parity; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 281 | `crate::trace::value(2, 0, aspis_core::field::WideExact::from_qm31(terminal));` | cfg(prover), excluded by deployed feature parity; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 282 | `crate::trace::value(` | cfg(prover), excluded by deployed feature parity; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 285 | `aspis_core::field::WideExact::from_qm31(masked_terminal),` | TX1:050 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 289 | `return Err(Error::EqualCirclePoints);` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 291 | `Ok(Verified {` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 292 | `roots: [*prefix.c1_root, prefix.payload(2)?.try_into().unwrap()],` | TX1:139 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
## TX1:137 verify_observed

Frozen source `crates/aspis-r1-cost-probe/src/r1_semantic.rs`:311, function text SHA256 `27205d3c1b0d1ae48ed5912d7cd971268c0721d1e6f16073d877ddd356aefa14`. Source order below includes std calls and cfg(prover) exclusions; native cuts not yet established.

| Line | Occurrence text | Cover / required frame |
|---|---|---|
| 312 | `let prefix = Prefix::parse(bytes)?;` | TX1:138 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 313 | `mark(obs, 0);` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 314 | `let mut transcript = public_transcript(public, hash, prefix.c1_root)?;` | TX1:131 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 315 | `let challenges = wire::begin(&prefix, &mut transcript)?;` | TX1:150 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 316 | `mark(obs, 1);` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 317 | `verify_finish(public, prefix, transcript, challenges, obs)` | TX1:136 OPEN; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
## TX1:087 prepare

Frozen source `crates/aspis-r1-cost-probe/src/candidate.rs`:255, function text SHA256 `d7248911c295b34282756b8084295f3355ee7384168ef17fa09cb74ee75bf48f`. Source order below includes std calls and cfg(prover) exclusions; native cuts not yet established.

| Line | Occurrence text | Cover / required frame |
|---|---|---|
| 256 | `let mut logical = aspis_core::r0::heap::filled(compact::LOGICAL_SEMANTIC + compact::LOGICAL_Y1, 0u8).map_err(¦_¦ Error::Allocation)?;` | TX1:064 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 257 | `let (semantic, y1) = logical.split_at_mut(compact::LOGICAL_SEMANTIC);` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 258 | `compact::expand_semantic(&proof[compact::OFF_SEMANTIC..compact::OFF_Y1], semantic)?;` | TX1:098 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 259 | `compact::expand_values(&proof[compact::OFF_Y1..compact::OFF_INACTIVE], y1)?;` | TX1:099 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 260 | `let v = wide_view(proof, &logical[..compact::LOGICAL_SEMANTIC], &logical[compact::LOGICAL_SEMANTIC..])?;` | TX1:095 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 261 | `let sem = crate::r1_semantic::verify_observed(public, v.semantic, hash, obs).map_err(¦_¦ Error::Semantic)?;` | TX1:137 OPEN; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 262 | `mark(obs, Phase::Semantic);` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 263 | `Prepared::new(&sem, &v, hash, g)` | TX1:010 CLOSED, TX1:023 CLOSED, TX1:055 CLOSED, TX1:063 CLOSED, TX1:107 CLOSED, TX1:110 CLOSED, TX1:143 CLOSED, TX1:167 CLOSED, TX1:174 CLOSED, TX1:176 CLOSED, TX1:179 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
## TX1:094 tx1

Frozen source `crates/aspis-r1-cost-probe/src/candidate.rs`:270, function text SHA256 `a92df9a63b1aa8083ec78d51a33f39dc937deaade3a936cd99052b4bc81a8e2d`. Source order below includes std calls and cfg(prover) exclusions; native cuts not yet established.

| Line | Occurrence text | Cover / required frame |
|---|---|---|
| 272 | `return Err(Error::Parse);` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 274 | `parse_shape(proof)?;` | TX1:086 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 275 | `canonical_scan(proof)?;` | TX1:084 OPEN; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 276 | `mark(obs, Phase::Parsed);` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 278 | `let p = prepare(public, proof, hash, obs, &mut g)?;` | TX1:087 OPEN; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 279 | `let a = Accumulator::new(Variant::S2)?;` | TX1:010 CLOSED, TX1:023 CLOSED, TX1:055 CLOSED, TX1:063 CLOSED, TX1:107 CLOSED, TX1:110 CLOSED, TX1:143 CLOSED, TX1:167 CLOSED, TX1:174 CLOSED, TX1:176 CLOSED, TX1:179 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 280 | `mark(obs, Phase::Prepare);` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 281 | `let folded_root: [u8; 32] = proof[compact::OFF_FOLDED_ROOT..compact::OFF_ROUND1].try_into().unwrap();` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 282 | `batch_merkle(proof, &p, &folded_root, 0, hash)?;` | TX1:081 OPEN; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 283 | `mark(obs, Phase::Merkle(0));` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 284 | `let geometry = QueryGeometry::for_range(&p.queries, 0, k)?;` | TX1:181 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 285 | `let pending = BatchedWeights::new(&a.weights)?;` | TX1:010 CLOSED, TX1:023 CLOSED, TX1:055 CLOSED, TX1:063 CLOSED, TX1:107 CLOSED, TX1:110 CLOSED, TX1:143 CLOSED, TX1:167 CLOSED, TX1:174 CLOSED, TX1:176 CLOSED, TX1:179 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 286 | `let (mut a, pending) = query_loop(proof, &p, a, &g, obs, &geometry, pending, k)?;` | TX1:088 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 287 | `pending.finish(&mut a.weights);` | TX1:066 CLOSED, TX1:106 CLOSED, TX1:109 CLOSED, TX1:175 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 288 | `let bytes = checkpoint(&p, &a, proof, public_bytes, hash);` | TX1:186 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 289 | `mark(obs, Phase::CheckpointWrite);` | TX1:130 CLOSED, TX1:191 CLOSED; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
| 290 | `Ok(bytes)` | parent std/control/cfg; cut required; SAME arguments; full Result; mutable footprint and immutable frame; first Err/abort stops suffix |
