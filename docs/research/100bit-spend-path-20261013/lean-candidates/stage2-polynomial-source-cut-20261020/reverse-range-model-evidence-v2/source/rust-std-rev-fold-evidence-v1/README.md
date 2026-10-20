# Pinned Rust `Rev<Range<usize>>::fold` source review

This folder pins four `core` source files from the Rust nightly used by the
candidate extraction. The source chain explains why the original fold visits
indices `6,5,4,3,2,1,0` on the x86_64 build host:

1. `Rev::fold` delegates to the wrapped iterator's `rfold` (`adapters/rev.rs`,
   lines 79–84).
2. `DoubleEndedIterator::rfold` runs a loop over `next_back` and invokes the
   callback once per returned item (`traits/double_ended.rs`, lines 305–315).
3. `Range<usize>::next_back` delegates to `spec_next_back` (`range.rs`, lines
   1113–1117). `usize` is among the `TrustedStep` types (lines 10–18), and the
   `TrustedStep` specialization decrements the exclusive end and returns it
   (lines 897–948). The 64-bit integer macro invocation includes `usize`
   (lines 438–440); the unsigned `Step` implementation uses predecessor
   subtraction (`range.rs`, lines 210–223 and 257–296).
4. Starting from `0..7`, those rules yield the finite item sequence
   `6,5,4,3,2,1,0`, then stop. That matches the candidate's seven explicitly
   ordered calls and the generated seven-bind body.

This is a pinned source-level derivation, not a Lean theorem about Rust's
standard library. The candidate still needs a formal source correspondence
or an adopted Rust source rewrite before the original-fold relationship can
be treated as closed. See `review.json` for toolchain and SHA-256 pins.
