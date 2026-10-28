# Static-form source association

These gates replace six local laws in the existing hybrid native/model bridges.
They do not replace a complete Rust leaf with a second implementation. The
existing Lean inductions consume exactly the local laws described below. No
new Lean axiom or whole-output premise is introduced.

Frozen source: `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`.
`KNF_SOURCE_PINS.json` pins the original field files and snapshots. KNF_field.rs
changes only the module path to KNF_wide_exact.rs; KNF_wide_exact.rs is verbatim.
Both snapshots contain the real WideExact representation and methods. No
replacement attribute or stub is used. In particular there are no own-copy
stubs and no alternative version of any KMX replacement. The exact KMX stubs
remain the inherited obligations of other gates; they are not needed here.

## Same source behaviour, different observation form

All six original harness function identifiers are retained. The new source
has no Observer alias, mark/value replacement, Option<fn>, function-pointer
value/comparison, ghost global or indirect observer. KNF_word and
KNF_transition are ordinary directly called functions. core::array::from_fn
uses statically dispatched concrete closures; it never receives an Option<fn>
value. Option<WideExact> is ordinary field decode success/failure data and is
not a function-pointer carrier. These are changed verification forms, not a
module/function rename experiment. No old verdict is promoted by renaming it.

- **LPm_K017 / parts_store**: the source prepared_claim assignment is literally
  `parts[point+1]=dot.finish()`, point<6. The old harness took arbitrary canonical
  E for the returned value. The new harness has the SAME seven E cells, arbitrary
  canonical initial cells and returned value, SAME point+1 assignment and arbitrary
  row/limb observation. Its generator fills the seven cells through direct calls
  in a loop instead of from_fn. Every valid E is attainable because from_limbs
  covers all eight canonical coordinates; no extra initial-state invariant is
  imposed. The selected-word equation for every row/limb gives the complete E
  carrier/frame equation: to_limbs enumerates all eight stored u32 fields.
  LPq's L064 parts update and the LPs/LPt consumer can use this identical law.
- **LPi_K015 / powers_final_iteration**: weights::powers<N> stores out[i]=p,
  increments i, returns immediately at i==N. Specializing N=7,i=6 gives exactly
  the source cut checked here. Every selected cell/word equals p at6 and the
  previous cell elsewhere; i=7. Only the irrelevant initial-state generator and
  observation form change. Pointwise equality replaces array-level memcmp and
  entails the same full returned carrier; no multiplication is reached.
- **LPi_K016 / powers_continue_prefix**: the same source cut at at<6 retains
  out[at]=p, exact index increment, frame and non-final branch. The next operands
  are exactly (p,x); BOTH operands' selected words are checked. The continuing
  multiplication/result law remains the inherited separately paired arithmetic
  law. No product is assumed or newly verified by this gate. The LPm powers
  trace and LPq powers owner port consume exactly these store/branch facts.
- **LPo_K008 / LPo_decode_words**: calls the verbatim WideExact::from_le_bytes
  method on EVERY32-byte array, with its actual from_limbs rejection and actual
  returned field. The reference word expression is the same source scalar
  u32::from_le_bytes(slice.try_into().unwrap()), factored into a directly called
  KNF_word function. A scalar local loop computes the eight-word validity
  conjunction, replacing the iter().all closure observation. Both Result arms
  are checked, and every returned limb equals its SAME input word. This
  discharges wide_view's decoder acceptance/value obligation unchanged; the
  overapproximate context decoder in other LPo gates remains separately paired.
- **LPk_K014 / LPk_byte_decode**: the SAME frozen sampler from_fn byte expression
  is factored through KNF_word; the selected decoded word equals the original
  shift/or polynomial for every byte input and word index. No table, fixture or
  canonical-word restriction is substituted. The LPk_Casts/model byte port can
  consume the same universal equality.
- **LPk_K011 / LPk_from_fn_order_word**: the original universal abstract closure
  admits an arbitrary complete next quotient and digit at each call. The new
  form expresses that transition as the directly called KNF_transition on the
  SAME mutable borrow. It has the same arbitrary next state/digit and no
  restriction between calls. Call index/count, indexed digit return, initial
  capture, consecutive input/output chaining and final capture are all checked.
  Specializing these arbitrary transitions to the real inner division traversal
  is exactly the inherited LPk association; its arithmetic/traversal laws are
  unchanged. LPp uses the restored LPk result, not a new sampled value.

The source cuts have no observable callback operation. weights::powers and
sampler::low_base_p_digits have no feature guard in these bodies. The
prepared_claim assignment is also unguarded. Deployed trace::value, outside
these local cuts, is a no-op because prover is absent; no enclosing observer
law or enclosing caller closure is inferred. The enclosing/native/SBF source
association remains the existing hybrid boundary.

## Features and compilation

All new Kani commands are standalone native helper gates. They compile neither
verifier.rs nor its Option<fn> observer. Each receipt records every resolved
crate's features from offline frozen-lock metadata with verifier
`default,private-leaf-salts,optimized-terminal,program-build` selected. This
workspace graph includes an unrelated spend-dynamic-rate512 feature; it is NOT
used as the canonical deployed graph or as body-identity evidence.

`KNF_FEATURE_BODY_AUDIT.json` retains the canonical isolated library-deployed
per-crate feature graph from NCS_I002 and checks the relevant body transfer.
Only actual core field definitions are compiled here; aspis-core's canonical
deployed features are exactly r0. Neither frozen field source contains a cfg
on r0. Every feature predicate in both field snapshots therefore has the same
truth value under the standalone empty feature set and deployed core:r0. The
ENTIRE field files (not merely an inventoried callee subset) have identical
selected bodies. The three reached WideExact methods have no cfg guards at all.
No statement method or verifier feature-dependent body is compiled by the
helper gates. This supplies the explicit rule15 body-identity qualification for
standalone helper extraction; it does not infer executable/ELF identity from
metadata. No no-entrypoint feature is selected.

Verbose compiler commands show edition2021, opt-level3 and overflow-checks=on.
The Cargo.lock is the pre-existing scratch crate's COPY of the frozen lock;
no linked/source lock is written. Every attempt checks its hash before/after
and validates each resolved package and edge against it before running Kani.

## Matched controls

For each pair the source differs only in `const KNF_XOR:u32=0` versus1.
The selected property asserts actual==expected^KNF_XOR. All control failures
are exactly this intended assertion, not bounds, unwind or representation
checks. Playback input vectors are retained in the full control stdout. These
are deliberately false specifications, not source failures needing native
replay. No positive gate failed; no timeout or rename receives credit.
