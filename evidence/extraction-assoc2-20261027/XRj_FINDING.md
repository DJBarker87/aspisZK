# Unchanged emitted Funs cannot elaborate against the coherent library

XRj_L013 is the first direct attempt on the byte-identical release Funs after
TypesExternal, Types and the current partial FunsExternal pass. Exit 1,
28.255235100979917 s, peak RSS 3584116 KiB, swaps 0. Full diagnostics are in
XRj_L013/stdout.log. This is not a timeout or a memory kill.

Missing externals remain and are listed separately in XRj_ELABORATION.json.
The following errors are independent of supplying more opaque release leaves:

* Lines 56,58,60: the generated mutable Iterator dictionary expects next to
  return (Option T,IterMut T); pinned IteratorIterMut.next returns a triple
  containing the restoration continuation. The self-name is also projected
  before application to T at step_by/enumerate.
* Lines 3693,3705: generated FnOnce call_once returns (U32,closure) where the
  trait requires U32; FnMut call_mut returns (U32,closure,closure->closure)
  where the trait requires (U32,closure).
* Lines 6053,6062,6066,6070,6141,6153 onward: a local Slice named compact
  shadows the namespace in compact.CodecError/expand_semantic_loop and
  COMPACT_SEMANTIC/LOGICAL_SEMANTIC references. These are identifier-resolution
  errors in the emitted body, not undefined library operations.

The generated file is unchanged. No alternate producer, adapted Funs,
compatibility attribute, changed FnOnce ABI, accepted sorry object or template
axiom is substituted. Its failed context is not a usable release object.
Therefore none of the six requested whole emitted-function association claims
can presently be checked; the chain is stopped under common rule 4. Independent
external definitions and per-iteration Kani work continue. Definitions and
bounded stage checks do not remove any actual-top premise.

Next deliverable requires a lead decision about a correctly associated
emission/toolchain or an explicitly authorized source-associated generated
adapter. This worker has zero extraction allowance and no authority to edit
generated files. A library change by itself cannot repair the namespace
shadowing and source-generated closure ABI errors without changing the frozen
input context. No source failure is hidden by substituting another module.
