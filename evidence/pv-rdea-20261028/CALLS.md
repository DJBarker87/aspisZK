# Deployed call-site reconciliation

The previous one-op30/one-op26 model inventory was not exhaustive. The current
machine/MIR/stdlib-inline evidence is linked from REPORT.md. Exact every-site
argument excerpts and hashes are in `site-reconciliation.json`; each of its 54
MIR source sites and 15 stdlib inline contexts is individually recorded.

| Site family | Argument source | Reachability/evidence | Proven request boundary |
|---|---|---|---|
| Durable reservation String constructor | literal 69, state_only_entropy.rs:961 | MIR candidate2, linked reserve_fallible allocation; SHA prelude/tail factor proved in actual FullFuns | `(0,69,1)` on success and allocator failure; physical fill adds no requests |
| Durable reservation join | store.directory; two hex digits for each of 32 SHA digest bytes, then `.burn` | MIR candidate2, machine call15ed45→GOT220e78→Path::_join | basename69 and relative branch; clone/append public schedule at physical byte boundary |
| Client recovery join | public caller-supplied outdir; literal `note-recovery.json` | MIR17, machine8252c | derived length18, relative branch |
| Client ledger join | outdir; literal `mask-nonce-ledger` | MIR17, machine827d8 | derived length17, relative branch |
| Client proof join | outdir; literal `proof.bin` | MIR17, machine82bca | derived length9, relative branch |
| Client statement join | outdir; literal `statement.bin` | MIR17, machine82c29 | derived length13, relative branch |
| fmt::format_inner constructor | `args.estimated_capacity()`: as_str length or decoded template literal lengths/placeholder metadata; rendered argument values not read by estimate | exact alloc bitcode inline location fmt.rs647; direct IR and ELF callers include devnet hex, plan::prove and anyhow formatting | decoded hex template capacity0; general physical constructor error law; native parser/provenance bridge incomplete |
| String::from_utf8_lossy constructor | input slice length; called only after invalid UTF-8 guard | exact alloc inline string.rs633; linked OS-error Debug/Display and addr2line::line::render_file xrefs | general constructor request law only; complete public invocation/length provenance not proved |
| Backtrace build-id constructor | `23+6+2*build_id.len()+1`; ELF metadata, debug directory guards | std inline elf.rs438; linked Mapping::new_debug and Cache::with_global callers | symbolic size formula; public metadata/guard classification still residual |
| Backtrace debuglink pushes | canonicalized object parent, filename from `.gnu_debuglink`, `.debug`, `/usr/lib/debug`, parent without leading slash | inline chains to locate_debuglink elf.rs470/471/478/479/480/488/489/490; exact contexts in JSON | physical push schedule depends on existing public header; source/header provenance residual |
| Backtrace debugaltlink push | canonicalized object parent plus ELF `.gnu_debugaltlink` filename, relative branch | inline chain to locate_debugaltlink elf.rs521 | physical push law; public-environment/header provenance residual |
| Backtrace split-DWARF pushes | optional `load.comp_dir`, then `load.path` from DWARF | inline chains elf.rs543/546 | physical push law; public-environment/header provenance residual |
| anyhow::ensure::render | msg length +2+formatted lhs length+4+formatted rhs length+1 | MIR0; absent resolved linked-function set | runtime candidate not certified unreachable; no source-public proof claimed |
| aspis_prover::pow::hex | bytes.len()*2 | MIR1; absent resolved linked-function set | runtime candidate not certified unreachable |
| itertools0.14 and0.15 generic join | separator length * iterator lower size_hint after first element | MIR19/20; generic implementation may be instantiated/inlined | not certified unreachable; caller/instantiation closure residual |
| num_cpus cgroup translate push | procfs mount point and relative cgroup path | MIR21; crate runtime unit but function not in resolved linked set | not certified unreachable |
| num_cpus raw_param join | self.base and quota/cgroup parameter string | MIR22; crate runtime unit but function not in resolved linked set | not certified unreachable |

MIR candidates3–16,18,23–36 are mechanically outside the runtime unit closure:
autocfg, cc, derivative, find_msvc_tools, proc_macro2, proc_macro_crate, syn,
toml and winnow sites. They cannot be invoked by spend entry points as runtime
Rust calls. Their exact dynamic arguments, literals, source spans and hashes are
still recorded individually in the JSON, rather than discarded. This is a
Cargo build/proc-macro boundary exclusion, not a linked-symbol heuristic.

A complete indirect-dispatch and inlining-coverage certificate is **not yet
established**. The conservative inventory retains those unknowns. Public outdir,
ELF metadata, OS locale/error buffers and filesystem-derived paths have not been
silently added to T as new assumptions; the needed native source classification
and actual endpoint simulation are explicit remaining deliverables.
