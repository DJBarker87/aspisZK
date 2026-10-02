# Selected Vec<U8>::extend source inventory

This read-only inventory records retained R160/R156 LLBC metadata, generated Lean call sites, and Rust standard-library source excerpts with exact line numbers and hashes. Lead confirmed on 2026-10-02 that all four inspected source file hashes match the NUC `nightly-2026-06-01` source snapshot.

The three generated call sites are listed in `generated-call-sites.txt`; source excerpts and hashes are listed in `inventory.json`. The important distinction is that R160 LLBC `fun 52` is the generic default `SpecExtend` implementation at `spec_extend.rs:17`. It is not the concrete `IntoIter` specialization at lines 31–38. The Rust source contains that specialization, but retained artifacts do not establish dispatch selection or extract its concrete body.

R160 `Vec::extend` (`fun 9`) is transparent with a structured body. Its generic `IntoIterator::into_iter` (`fun 12`), `Vec::into_iter` (`fun 53`), generic-default `SpecExtend::spec_extend` (`fun 52`), `IntoIter::next` (`fun 226`), and `IntoIter::fold` (`fun 233`) are Foreign/Opaque. R156 `Vec::extend` and corresponding iterator functions are opaque; no explicit SpecExtend function appears in its LLBC.

Retained extraction history shows R160’s `--include alloc::vec::_::extend` command and R185’s `--monomorphize` command, but no recorded selector for the concrete SpecExtend specialization or Vec::into_iter. R185 translation stopped at the nested-loop Option-language-item diagnostic before Lean generation. Potential pointer obligations are listed as source locations only; there is no pointer-refinement claim here.
