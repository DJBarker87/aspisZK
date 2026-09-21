#!/usr/bin/env python3
"""Create a disposable channel-opening differential-check stage.

The input quadratic-channel stage is copied and never modified.  The output
adds a distinct checker cfg and compares the actual staged ``opened_channel``
implementation with the old two-channel ``opened`` result on the existing
authenticated-record corpus.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
from pathlib import Path

EXPERIMENTS = "docs/research/v8-no-work-100-20260907/experiments"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--stage", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    stage, output = a.stage.resolve(), a.output.resolve()
    if output.exists():
        raise SystemExit(f"refusing to overwrite {output}")
    manifest = json.loads((stage / "r18-stage.json").read_text())
    for name, expected in manifest["files"].items():
        path = stage / name
        if not path.is_file() or sha(path) != expected:
            raise SystemExit(f"channel manifest mismatch: {name}")
    host = stage / EXPERIMENTS / "r17_host_relation.rs"
    if "pub(super) fn opened_channel" not in host.read_text():
        raise SystemExit("input is not a quadratic-channel stage")
    corpus = Path(__file__).with_name("r19_opening_check.rs")
    if not corpus.is_file():
        raise SystemExit(f"missing source corpus: {corpus}")

    shutil.copytree(stage, output)
    root = output / EXPERIMENTS
    source = corpus.read_text()
    start, end = source.index("fn compare("), source.index("pub(super) fn run", source.index("fn compare("))
    compare = '''fn compare(w:&Wire<'_>,p:&Prefix,g:[K;2],ids:&[u32],a:K)->Result<([Vec<K>;2],Vec<M31>),Error>{
    let old=r17_relation::opened(w,p,g,ids,a);
    let betas=[K::ZERO,K::ONE,K::ONE.neg(),p.gamma,p.iv[0],p.iv[1]];
    for beta in betas {
        let fresh=r17_relation::opened_channel(w,p,g,ids,a,beta);
        match (&old,&fresh) {
            (Ok((old_values,old_xs)),Ok((new_values,new_xs)))=>{
                assert_eq!(new_xs, old_xs, "channel x coordinates");
                let expected=old_values[0].iter().zip(&old_values[1])
                    .map(|(&r,&g)|crate::r19_channel_fold::lerp(r,g,beta)).collect::<Vec<_>>();
                assert_eq!(*new_values,expected,"opened_channel beta");
            }
            (Err(old_error),Err(new_error))=>assert_eq!(new_error,old_error,"error path beta"),
            (old_result,new_result)=>panic!("channel result mismatch beta={beta:?}: old={old_result:?} new={new_result:?}"),
        }
    }
    old
}
'''
    source = source[:start] + compare + source[end:]
    source = source.replace(
        'R19_OPENING source_arbitrary_authenticated=32 canonical_positions=3344 chord_poles=88 roots=52 record_mutations=88 query_indices=22 frontier_nodes=all wrapper_error_order=true reference_retained=true',
        'R19_CHANNEL_OPENING source_arbitrary_authenticated=32 betas=6 canonical_positions=3344 chord_poles=88 roots=52 record_mutations=88 query_indices=22 frontier_nodes=all wrapper_error_order=true reference_retained=true',
    )
    (root / "r19_channel_opening_check.rs").write_text(source)

    callback = root / "relation_callback.rs"
    callback_text = callback.read_text()
    old_main = "#[cfg(v8_performance)]\nfn main(){payment_extraction::performance::run();}"
    new_main = "#[cfg(all(v8_performance,not(r19_channel_opening_check)))]\nfn main(){payment_extraction::performance::run();}"
    if old_main not in callback_text:
        raise SystemExit("channel callback performance main anchor missing")
    callback_text = callback_text.replace(old_main, new_main, 1)
    callback_text += ("\n#[cfg(r19_channel_opening_check)]\n"
                      "mod r19_channel_opening_check;\n"
                      "#[cfg(r19_channel_opening_check)]\n"
                      "fn main(){r19_channel_opening_check::run();}\n")
    callback.write_text(callback_text)
    # Keep the copied R18 manifest complete for the disposable checker stage:
    # callback is modified and the distinct checker is newly added.  Preserve
    # the channel stage's original profile metadata while refreshing only the
    # affected file hashes.
    out_manifest = json.loads((output / "r18-stage.json").read_text())
    if "quadratic-channel-fold" not in out_manifest.get("profile", ""):
        raise SystemExit("input manifest is not the quadratic-channel channel profile")
    out_manifest["files"][str((root / "relation_callback.rs").relative_to(output))] = sha(callback)
    checker_path = root / "r19_channel_opening_check.rs"
    out_manifest["files"][str(checker_path.relative_to(output))] = sha(checker_path)
    (output / "r18-stage.json").write_text(json.dumps(out_manifest, indent=2) + "\n")
    metadata = {
        "input_stage": str(stage),
        "input_r18_manifest_sha256": sha(stage / "r18-stage.json"),
        "channel_host_sha256": sha(host),
        "checker": "r19_channel_opening_check",
        "cfg": "r19_channel_opening_check",
        "betas": ["0", "1", "-1", "gamma", "iv[0]", "iv[1]"],
        "corpus": "r19_opening_check.rs transformed; canonical/error/domain/auth mutations retained",
        "source_hashes": {
            "r17_host_relation.rs": sha(output / EXPERIMENTS / "r17_host_relation.rs"),
            "relation_callback.rs": sha(callback),
            "r19_channel_opening_check.rs": sha(root / "r19_channel_opening_check.rs"),
        },
    }
    (output / "r19-channel-opening-check.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(json.dumps({"stage": str(output), "checker": metadata["checker"], "input_unchanged": True}))


if __name__ == "__main__":
    main()
