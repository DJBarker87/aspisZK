Z8d -- the coefficient basis of the D word and the x^28 law (LOG D21.6)
=====================================================================

Base 88a5bb4e3. Branch codex/z8d-basis-20261015. Exact M31/QM31/WideExact
computation; not a Lean proof; no Lean or production source changed. Lead
converts this text to .md.

STOP: none. The control (Z8c's D-high_bal block, run verbatim) gives 1,808
on every vector, as Z8c did, and so does the generic re-derivation with
natural-coefficient constraints. The stop rule was not triggered. Every Z8d
line (110 per job) is identical on vectors 0-4 after removing labels and
timings. Pass 1 re-measures silent 1,076 and bat(ker own) 1,912 with the 25
relations exact (0 violations on 16,542 carries per job).

Answer in one paragraph. Lean and the probe index the D message by the
same NATURAL (Chebyshev-product) basis. Z8c's D-high was therefore "natural
coefficients < 56 zero", not "divisible by x^28". The design's §2.5.1 is
written in the monomial basis. Rerun in the monomial basis, the x^28 step
itself holds: the quotient of an OOD-zero, X^28-divisible message is
X^28-divisible, checked directly. The fold reads natural coordinates,
however, so the low fibres do not vanish. Monomial D-high gives 1,792
(not 1,800). f0..f13 all fail, and its image reaches all 14 low fibres in
full (f-prefix rank 8m for every m <= 128). Monomial D-high is also not
inside ker R_D: R_D has rank 216 on it. Intersected with ker R_D it gives
1,700. Neither reading gives 1,800 with f0..f13 holding, so under D21.6
§2.5 has to be revised. G-low in monomial coordinates is 224 with and
without G's extra claim. Every D-high variant plus G's
(ker R_G ∩ ker own_G) image assembles to 1,912 = bat(ker own).

1. Basis identification (item 1)
--------------------------------
Paths: LEAN0 = docs/research/v8-r0-zk-20261009/lean, WREF =
docs/research/v8-wide-reference-20261005/lean, AF = AspisFormal/AspisFormal,
R0 = crates/aspis-core/src/r0, Z4 = docs/research/v8-r0-zk-20261009/z4.

Lean, from the tape to the polynomial:
 (a) dWord B tape = balance 0 (extensionRaw B tape 2) : Fin 1024 -> K is a
     ROW-indexed column (LEAN0/R0Z/MaskLayout.lean:91-92); it is trace column
     28 in applyAff (MaskLayout.lean:116). No basis is involved yet.
 (b) Rows become message coefficients by the transport permutation only:
     coeffsLinear pi m = fun j => m (pi.symm j) (LEAN0/R0Z/HonestView.lean:80-84;
     same as R0P coeffsOf, docs/research/v8-r0-sem-proof-20261008/lean/R0P/
     SemView.lean:32-33). batchLinear feeds coeffsLinear pi of each column to
     quotientLinear (HonestView.lean:184-193). Index j of InitialMessage is
     therefore the coefficient index k of design §2.5 and of Z8c.
 (c) The message is read in the NATURAL basis:
     p0Linear / p1Linear = naturalLinear on the even / odd coefficients
     (WREF/R0/PolynomialPair.lean:76-80), equal to initialP0 / initialP1
     (AF/V5FriInitialCircleEncoderIdentity.lean:124-129);
     naturalCoefficientPolynomial c = monomialPolynomial (naturalCoeffMatrix *v c)
     (AF/V5FriConcreteEncoderApplicability.lean:276-296);
     naturalCoeffMatrix K m [d, j] = [X^d] naturalLinePoly K j
     (AF/CircleNaturalBasis.lean:43-45);
     naturalLinePoly K j = prod_{b in bits j} T_{2^b} (Chebyshev)
     (AF/CircleNaturalBasisEval.lean:39-40).
     evalMessage (WREF/R0/Chord.lean:34-35), exactInitialEncoder
     (WREF/Wide/InitialEncoder.lean:32-39) and oodLinear ("R0/Chord.evalMessage
     in the exact natural coefficient basis", HonestView.lean:105-107) all go
     through initialP0/initialP1.
 (d) The fold reads natural coordinates directly:
     foldMessage alpha q = coefficientFoldLayer 256 alpha q (WREF/R0/Fold.lean:71-72)
     = (sum_s alpha^s q (childIndex d s))_d with childIndex d s = 4d+s
     (AF/V5ComponentCConcreteFoldLinearity.lean:173,215-217,238-240;
     HonestView.lean:205-206 foldLinear).
Rust (the probe calls these):
 (e) encoder::eval_pair: p0 = sum_j q[2j] N_j(x), p1 = sum_j q[2j+1] N_j(x),
     N_j from basis::values (R0/encoder.rs:10-19); values builds
     N_{w+j} = N_j * D_{log2 w} with D_0 = x, D_{b+1} = 2 D_b^2 - 1
     (R0/basis.rs:7-19, 37-49), i.e. N_j = prod_{b in bits j} T_{2^b}(x), the
     same basis as Lean's naturalLinePoly. NaturalBasis::matrix is
     M[d, j] = [X^d] N_j, row-major (R0/basis.rs:70-76, 93-155);
     natural_to_monomial = M * c, monomial_to_natural = M^-1 * c
     (R0/basis.rs:167-182). fold::fold_message is the coefficient fold
     out[d] = combine(alpha, q[4d..4d+4]) (R0/fold.rs:40-42, 61-67).
 (f) Z8c: rows_hi = COEFFICIENT_TO_ROW[56..1024] (Z4/z8c.rs:1068) and the unit
     functionals quotient the natural unit e_k (Z4/z8c.rs:265-292, prover::quotient
     on natural messages). Z8c's "c_k = 0 for k < 56" is therefore "natural
     coefficients 0..55 zero", i.e. p0, p1 in span{N_j : j >= 28}.

Change of basis. For p in {0, 1} (p0, p1), the monomial coefficient of X^d is
  P_p[d] = sum_{j >= d} M[d, j] c[2j + p],   M upper triangular, M[j, j] != 0,
so "p0, p1 divisible by X^28" is the 56 K-linear (224 F-limb) conditions
P_p[d] = 0 for d < 28, p = 0, 1; each reads every natural coefficient j >= d
of its parity. It is not a coordinate condition in Lean's index, and it is a
different 968-dimensional subspace from Z8c's natural-high space: N_28 =
T_4 T_8 T_16 has N_28(0) = 1, so it is not divisible by X, and X^28 itself
has natural coefficients below 28 (both printed per job in Z8D_X28, §2).

Where the design's argument lives. §2.5.1 writes c = x^28 (p~0 + y p~1) with
"even index 2i <-> x^i in p0, odd 2i+1 <-> x^i in p1": the MONOMIAL basis,
which neither Lean nor Rust uses for the message index. Its first step
(ood(c) = 0 and c = x^28 p~ imply Q(c) = x^28 Q~ as polynomials) is a statement
about polynomials and does not depend on coordinates. Its conclusion
"Q(c)_k = 0 for k < 56, so foldMessage alpha (Q c) d = 0 for d < 14" uses k
in two senses: monomial for the divisibility, natural for foldMessage, which
reads natural coordinates (d). The two "low" subspaces differ, so in neither
basis does the argument give f0..f13 = 0 as stated. §2 measures both readings.

2. D-high (item 2; structure A, vectors 0-4, all identical)
-----------------------------------------------------------
Sources: control = Z8c's block verbatim (rows pi^-1(56..1023); e_r active,
e_r - e_303 inactive; 3,868 sources). The other three use all 4,092
balanced D sources of Lean `balance 0` (e_r for active r, e_r - e_0 for
inactive r != 0). Constraints are [low (224 limbs) | own_D (376) | R_D
(1,084) if "kerR"]. "low" is natural coefficients 0..55 or monomial
P_p[d], d < 28 (Z4/z8d.rs `low_of`; the e_0 term contributes at
coefficient pi(0) = 89, which has monomial low components).

 kind                    | low rk | own on high | R_D on high∩ker own | bat rank | ia piv | annihilator | relations hold | f0..f13 | unexplained
 ------------------------+--------+-------------+---------------------+----------+--------+-------------+----------------+---------+------------
 control_z8c_natural     |   --   |     372     |   0 (asserted)      |  1,808   |   0    |    304      | 25/25 (200)    | all fail|   104
 natural_generic_kerR    |  224   |     372     |   0                 |  1,808   |   0    |    304      | 25/25 (200)    | all fail|   104
 monomial_x28            |  224   |     376     |  (not imposed)      |  1,792   |   0    |    320      | 25/25 (200)    | all fail|   120
 monomial_x28_kerR       |  224   |     376     |  216                |  1,700   |   0    |    412      | 25/25 (200)    | all fail|   212
 design §2.5.1 prediction                                             |  1,800   |        |    312      | 25 + f0..f13   | hold    |     0

 Rows on which each f_d is nonzero (out of the image's echelon rows):
   control / natural_generic: f0..f7 56, f8..f13 64 (as Z8c).
   monomial_x28: f0 56, f1 64, ..., f13 160 (step 8).
   monomial_x28_kerR: f0..f3 56, f4..f7 60, f8..f13 68.
 Projection ranks of the image onto f[0..m) for m = 1,2,4,8,12,13,14,15,16,20,24,32,64,128,256;
 h rank in brackets:
   control, natural_generic: 8,8,8,8,16,16,16,24,32,64,96,160,416,928,1776  [48]
   monomial_x28:             8,16,32,64,96,104,112,120,128,160,192,256,512,1024,1760  [48]
   monomial_x28_kerR:        8,8,8,12,20,20,20,28,36,68,100,164,420,932,1668  [48]
 So monomial D-high reaches the 14 low fibres in full (112 limbs). Its
 120-limb deficit lies elsewhere. The natural D-high (Z8c's) reaches only 16
 limbs of them.

 Remainder support. For every kind the union support of the unexplained
 remainder is [h2..h6, f22..f255]. That set is exactly the complement of
 the pivots of the 25 explained relations: ia; S1 at h0; S2 - S1 at h1;
 the 22 S3_u at f0..f21. A generic remainder reduced modulo those
 relations always has this support, so it carries no structural
 information. The same holds for Z8c §5's [h2..h6, f22..f255], which D21.6
 named as the input to a §2.5 revision. The remainder is dense. Also,
 left_kernel_report (copied from z8c.rs) prints "pivot=" as the first
 nonzero position of each unreduced residual, so repeated labels such as
 "h2:0" are not distinct echelon pivots. The rank and the union support are
 computed from a proper echelon form and are correct.

 Direct check of §2.5.1 on the quotient (Z8D_LAW; 3 random OOD-zero messages
 per basis per job, WideExact, prover::quotient, fold::fold_message):
   high in    | input nat-low≠0 | input mono-low≠0 | Q nat-low≠0 | Q mono-low≠0 | Q fold f0..f13≠0
   natural    |       0/56      |      56/56       |    56/56    |    56/56     |     14/14
   monomial   |      56/56      |       0/56       |    56/56    |     0/56     |     14/14
 The monomial row confirms the polynomial step of §2.5.1 (Q(x^28 p~) =
 x^28 Q~) and refutes its fold step: foldMessage reads natural coordinates,
 and a nonzero X^28-divisible polynomial has nonzero natural coefficients
 below 28. Example (Z8D_X28): X^28 = sum of N_j over j in {0, 2, ..., 28}
 with nonzero coefficients, and N_28 has nonzero monomial coefficients at
 the same 15 degrees (N_28(0) = 1).

 Reading. In no basis in which the D word can be written does "c low
 coefficients zero" imply "f0..f13 of bat = 0". In the natural basis the
 hypothesis is a coordinate condition, it lies in ker R_D, and it misses
 104 limbs. Those limbs are not the f0..f13 coordinates. In the monomial
 basis the quotient law holds, but the fold does not see it, D-high is not
 round-free (R_D rank 216), and it misses 120 limbs, or 212 inside ker R_D.
 A statement that makes "f_d(Q c) = 0 for d < 14" true is
 Q(c) ∈ span{N_j : j >= 28} (natural-high quotient). That is the
 z-dependent space c ∈ L·(natural high) and not a coordinate condition on
 c. I derived this and did not measure it.

3. G-low (item 3; ker R_G ∩ ker own_G; all vectors identical)
-------------------------------------------------------------
 variant           | kernel dim | natural rows pi^-1(0..55) | monomial low (P_p[d], d<28) | low folds f0..f13 | joint nat+fold | joint mono+fold
 own_all           |   3,064    | 220 (Z8c 220)             | 224                         | 112               | 236            | 336
 own_without_extra |   3,068    | 224 (Z8c 224)             | 224                         | 112               | 240            | 336
 G's extra claim is libraWeight on NATURAL coefficients k < 56. It costs one
 K4 line in natural coordinates and nothing in monomial coordinates.
 Monomial low and the low folds are jointly free (336 = 224 + 112). G's
 batched image on the kernel: 1,904, with full f-prefix ranks (8m), as in Z8c.
 Assembly (own_all kernel): rank of bat(D-high variant) + bat(G kernel) =
 1,912 = bat(ker own) for all four D-high variants (control, natural_generic_kerR,
 monomial_x28, monomial_x28_kerR). (B) is reached in every case. The split
 between the two absorbers is not the f0..f13 split, in either basis.

4. Code
-------
z8d.rs is a module of probe.rs dispatched by `--z8d`. The probe.rs change
is the `mod z8d` declaration and one dispatch line. z8c.rs is unchanged
(byte-identical to 88a5bb4e3). z8d.rs is z8c.rs lines 21-1198 (helpers and
main through pass 1) copied verbatim, with print tags renamed Z8C_ -> Z8D_,
plus `#![allow(dead_code)]`. Pass 2, PR6/PR7 and (i')/(ii') are not run. New
code: Z8D_X28, law_check (Z8D_LAW), low_of (natural or monomial low
functionals of a balanced source, from NaturalBasis::matrix), the control
block (z8c's D-high_bal code verbatim), the three generic D-high runs, and
the G-low block, which is z8c's code with monomial-low carries and
assemblies added. run-z8d.py is run-z8c.py with mode z8d, a parser for the
new tags, default structure A, and base 88a5bb4e3.
All 5 CHALLENGE lines match probe-C.log.

5. Runs and receipts
--------------------
Host dombarker@100.108.41.90, staging
/home/dombarker/project-offloads/aspis-z8d-20261015/ (fresh; repo/ = rsync of
Cargo.toml, crates/aspis-{core,statement,prover}, z4/ without target/ and
run directories). Release profile opt-level=3 with overflow-checks; rustc as
recorded in evidence-Z8d.json. The Lean workspace and its lock were not
touched. Local work was `cargo check` only.

Scope check. Before the preflight, no aspis scope was active. The full run's
launch command lists scopes first, and it showed one active transient scope
from another job: run-r8ab31e2dda9347cf84cea4d15eaa2644.scope, a
/usr/bin/timeout 900 Lean replay of aspis-r1-concrete-decoder-20261013. My
launch did not gate on that check, so the full run started while that scope
was active. Checked moments later, that scope had already exited; only
aspis-z8d-full (MemoryMax 4 GiB) was active, with 51 GiB available. I did not
touch the r1 job. The overlap was a short Lean check, and my reservation
was 4 GiB.

  cd /home/dombarker/project-offloads/aspis-z8d-20261015/repo
  /usr/bin/time -v -o ../preflight-time.txt systemd-run --user --scope --unit=aspis-z8d-preflight \
    -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
    python3 docs/research/v8-r0-zk-20261009/z4/run-z8d.py \
    --out /home/dombarker/project-offloads/aspis-z8d-20261015/preflight-evidence --preflight
  /usr/bin/time -v -o ../full-time.txt systemd-run --user --scope --unit=aspis-z8d-full \
    -p MemoryHigh=3G -p MemoryMax=4G -p MemorySwapMax=0 \
    python3 docs/research/v8-r0-zk-20261009/z4/run-z8d.py \
    --out /home/dombarker/project-offloads/aspis-z8d-20261015/full-evidence --vectors 5 --jobs 5

 scope / target        exit  wall s     peak child RSS KiB  cgroup peak B    swap
 preflight / compile   0     54.984     545,400             889,159,680      0
 preflight / A-0       0     344.670    339,560             889,159,680      0
 preflight scope total 0     6:39.75 (time -v), max RSS 545,400 KiB, swaps 0
 full / compile        0     0.059      28,852              26,898,432       0
 full / A-0            0     508.981    339,216             1,691,353,088    0
 full / A-1            0     437.6      340,020             1,691,353,088    0
 full / A-2            0     487.5      339,688             1,691,353,088    0
 full / A-3            0     494.6      338,992             1,691,353,088    0
 full / A-4            0     501.5      338,576             1,691,353,088    0
 full scope total      0     8:29.15 (time -v), max RSS 340,020 KiB, swaps 0
 cgroup swap peak 0 in every receipt. 5 jobs ran concurrently.
 The preflight A-0 output equals the full run A-0 output line for line, except for
 the preflight flag (timings removed).
 No Lean was run, so #print axioms does not apply.

6. Source SHA-256
-----------------
evidence-Z8d.json records 210 source SHA-256s; all match this worktree.
Key files (Z4 = docs/research/v8-r0-zk-20261009/z4, R0 = crates/aspis-core/src/r0):
 c4677e77bddcb7dcb9092e7342e66d24540925238801481e11b58e42f2358aa8  Z4/z8d.rs
 0bbedbc882062d51817e207b4882daa52f35a5795cdc84221fb96e433b456625  Z4/z8c.rs
 a2dde3aa6ed7dacd773777a12994b52b1d938eef40e0ee661a251697d2457638  Z4/probe.rs
 61de771380fdb0013ee3c9b07af0b946bf9fb2e9e3c7af96e20c0e93463f1be4  Z4/run-z8d.py
 966273329a3897b42e9435085d9eed8b79ec8380630dbdffd3549ed9bba185ad  Z4/Cargo.toml
 7ef1459de53451f93bdf4ae30a4ff70201cce89027fd1fedf0c6b8a1c6d712f9  Z4/Cargo.lock
 82d04e864271eb2eca59888282d2a615b697e138afb0cb2a1ef002cc9324830c  Z4/probe-C.log
 f557751312781a0dec538b9b3934436e20644f4430144c5a612cfe6bc8d06166  R0/basis.rs
 6e34b6b2b264573e63f963fe2879d05eaed4f767e105bf7ca0c79d5b6dfc5c88  R0/encoder.rs
 06afbfb2c1c03306b59136695fdbf89382e21ed420f123982a70e977c2f35e39  R0/fold.rs
 4d4d8634bcb872d372bd430ac56cd60aece6d60e87e505126ce9ab46d2ef6c28  R0/prover.rs
 b3a3d096fec5f307613ad87525eea452bae5c13080a7f52816e0dc0b986f1868  R0/chord.rs
 ac892fa35fd6a8d697805770ece27fde79d1b91db619323870dff603b4f3045d  R0/transport.rs

Artifacts: z8d.rs, run-z8d.py, summary-Z8d.json, evidence-Z8d.json,
probe-Z8d.log (5 job logs concatenated), z8d-runs/ (driver logs, compile
logs, time -v outputs, preflight A-0 log and evidence).
