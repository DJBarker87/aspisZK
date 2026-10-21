#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_middle::{mir::TerminatorKind, ty::{self, TyCtxt}};
use std::{env, fs::File, io::Write};

struct Probe;
impl Callbacks for Probe {
    fn after_analysis<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let module = env::var("S10_MODULE").unwrap();
        let mut out = File::create(env::var("S10_OUTPUT").unwrap()).unwrap();
        // Optimization of a parent can steal its closure's elaborated body.
        // Snapshot the selected module before optimizing any selected body.
        let mut before_bodies = std::collections::HashMap::new();
        for local in tcx.mir_keys(()) {
            let def = local.to_def_id();
            let path = tcx.def_path_str(def);
            if module != "*" && !path.starts_with(&format!("{module}::")) { continue; }
            if matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Fn |
                rustc_hir::def::DefKind::AssocFn | rustc_hir::def::DefKind::Closure) {
                let body = tcx.mir_drops_elaborated_and_const_checked(*local);
                if !body.is_stolen() { before_bodies.insert(*local, body.borrow().clone()); }
            }
        }
        for local in tcx.mir_keys(()) {
            let def = local.to_def_id();
            let local_path = tcx.def_path_str(def);
            let crate_name = tcx.crate_name(def.krate).to_string();
            let path = if local_path.starts_with(&format!("{crate_name}::")) { local_path }
                else { format!("{crate_name}::{local_path}") };
            let parts: Vec<_> = path.split("::").collect();
            if module != "*" && parts.get(1).copied() != Some(module.as_str()) { continue; }
            let span = tcx.sess.source_map().span_to_diagnostic_string(tcx.def_span(def));
            writeln!(out, "D\t{:?}\t{:?}\t{:?}", path, span, tcx.generics_of(def)).unwrap();
            if !matches!(tcx.def_kind(def), rustc_hir::def::DefKind::Fn |
                rustc_hir::def::DefKind::AssocFn | rustc_hir::def::DefKind::Closure |
                rustc_hir::def::DefKind::Ctor(..)) {
                writeln!(out, "K\t{:?}\t{:?}", path, tcx.def_kind(def)).unwrap();
                continue;
            }
            let mut phases = Vec::new();
            if let Some(before) = before_bodies.get(local) { phases.push(("elaborated", before)); }
            else { writeln!(out, "E\t{:?}\t{:?}", path, "elaborated body already consumed by compiler query").unwrap(); }
            phases.push(("optimized", tcx.optimized_mir(def)));
            for (phase, body) in phases {
            writeln!(out, "P\t{:?}\t{:?}", path, phase).unwrap();
            for scope in body.source_scopes.iter() {
                if let Some((instance, call_span)) = scope.inlined {
                    writeln!(out, "L\t{:?}\t{:?}\t{:?}", path, format!("{instance:?}"),
                        tcx.sess.source_map().span_to_diagnostic_string(call_span)).unwrap();
                }
            }
            for (bb, block) in body.basic_blocks.iter_enumerated() {
                let term = block.terminator();
                let site = tcx.sess.source_map().span_to_diagnostic_string(term.source_info.span);
                match &term.kind {
                    TerminatorKind::Call { func, args, .. } => {
                        let ty = func.ty(&body.local_decls, tcx);
                        match ty.kind() {
                            ty::FnDef(target, generics) => writeln!(out,
                                "C\t{:?}\t{:?}\t{:?}\t{:?}\t{:?}\t{:?}",
                                path, bb, format!("{}::{}", tcx.crate_name(target.krate), tcx.def_path_str(*target)), format!("{generics:?}"), site,
                                format!("{args:?}")).unwrap(),
                            _ => writeln!(out, "I\t{:?}\t{:?}\t{:?}\t{:?}", path, bb, format!("{func:?}: {ty:?}"), site).unwrap(),
                        }
                    }
                    TerminatorKind::Drop { place, .. } => writeln!(out,
                        "X\t{:?}\t{:?}\t{:?}\t{:?}", path, bb,
                        format!("{:?}", place.ty(&body.local_decls, tcx).ty), site).unwrap(),
                    _ => {}
                }
            }
            // Keep MIR for independent inspection of indirect-register provenance.
            writeln!(out, "B\t{:?}\t{:?}", path, format!("{body:#?}")).unwrap();
            }
        }
        Compilation::Stop
    }
}
fn main() {
    let mut args: Vec<String> = env::args().collect();
    // RUSTC_WORKSPACE_WRAPPER supplies the real rustc path as argv[1].
    if args.get(1).is_some_and(|s| s.ends_with("rustc")) {
        let real = args.remove(1);
        let selected = args.windows(2).any(|a| a[0] == "--crate-name" &&
            a[1] == env::var("S10_CRATE").unwrap());
        if !selected {
            let status = std::process::Command::new(real).args(&args[1..]).status().unwrap();
            std::process::exit(status.code().unwrap_or(1));
        }
    }
    rustc_driver::run_compiler(&args, &mut Probe);
}
