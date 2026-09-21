#!/usr/bin/env python3
"""Source-pinned, isolated R18 sparse-G profile, current T unchanged.

This first stage retains the dense G reference/verification path for source
screening. It is not the compact performance implementation or a privacy proof.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

from reconstruct_generated_inputs import EXPERIMENTS, one_replace
from stage_r17_two_channel_host import function_body

PROFILE = "AV8/R18/sparse-coded-G128-step3/two-channel/research-v1"
BASE = "6677d5f1310ff7373301fbd79f186278f772e68a"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--repo", type=Path, required=True)
    p.add_argument("--stage", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    a = p.parse_args()
    assert not a.output.exists(), "fresh output only"
    revision = subprocess.check_output(["git", "-C", str(a.repo), "rev-parse", "HEAD"], text=True).strip()
    subprocess.run(["git", "-C", str(a.repo), "merge-base", "--is-ancestor", BASE, revision], check=True)
    control = json.loads((a.stage / "r17-compact-control.json").read_text())
    for name, expected in control["files"].items():
        assert sha(a.stage / EXPERIMENTS / name) == expected, name
    for name, expected in control["core_files"].items():
        assert sha(a.stage / name) == expected, name
    probe = json.loads((a.stage / "r17-sbf-probe.json").read_text())
    assert "cyclic_g" in probe and "carry_shortcuts" in probe, "preferred R43 predecessor"
    assert "compact_g" not in probe, "do not use the slower geometric profile"
    source = a.repo / "docs/research/v8-full-view-zk-20260912/tools"
    adapter = probe["workspace_adapter"]["r17_structured_g.rs"]
    assert sha(source / "r17_structured_g.rs") == adapter["before_sha256"]
    assert sha(a.stage / EXPERIMENTS / "r17_structured_g.rs") == adapter["after_sha256"]
    shutil.copytree(a.stage, a.output)
    root = a.output / EXPERIMENTS
    changes = {}

    def edit(name, transform):
        path = root / name
        before = sha(path)
        path.write_text(transform(path.read_text()))
        changes[name] = dict(before_sha256=before, after_sha256=sha(path))

    def structured(s):
        s = function_body(s, "pub(super) fn mixing_row(", lambda _: """
    assert!(i < COINS);
    let mut out=vec![K::ZERO;N];
    out[super::basis_transport::transport().order[super::r18_sparse_coded_g::slot(i)]]=K::ONE;
    out
""")
        s = function_body(s, "pub(super) fn mixed_coins(", lambda _: """
    assert_eq!(g.len(),N);
    // Prover/host only. The SBF compact path uses caller-owned slices.
    core::array::from_fn(|i|g[super::basis_transport::transport().order[super::r18_sparse_coded_g::slot(i)]])
""")
        return function_body(s, "pub(super) fn mask_weights(", lambda _: """
    // Dense independent reference: scatter exactly the same semantic coins.
    let mut coins=vec![K::ZERO;COINS];
    let mut out=vec![K::ZERO;N];
    super::r18_sparse_coded_g::original_weights_into(point,
        super::basis_transport::transport().order.as_slice().try_into().unwrap(),&mut coins,&mut out);
    out
""")

    edit("r17_structured_g.rs", structured)
    edit("relation_callback.rs", lambda s: one_replace(s, "mod r17_structured_g;",
        "mod r17_structured_g;\nmod r18_sparse_coded_g;", "sparse module"))
    # The optimized dense reference used a separate FFT implementation. Replace
    # that caller as well: changing only semantic coins would be inconsistent.
    edit("r17_mask_workspace.rs", lambda _: """// R18 dense source-screening adapter; not the compact primary terminal.
use super::corelib::field::QM31 as K;
pub(super) fn mask_weights_into(z:&[K;10],coins:&mut[K;271],out:&mut[K;1024]) {
    super::r18_sparse_coded_g::original_weights_into(z,
        super::basis_transport::transport().order.as_slice().try_into().unwrap(),coins,out);
}
""")
    old = "AV8/R17/structuredG271-two-channel/compact-binding-research-v2"
    for name in ["performance_verifier.rs", "payment_extraction.rs"]:
        edit(name, lambda s: one_replace(s, old, PROFILE, "new profile from transcript initialization"))
    edit("r17_host_relation.rs", lambda s: one_replace(one_replace(s,
        "AV8/R17/compact-functional/Vandermonde1024-nodes1to1024/271-coins/two-channel/v2",
        "AV8/R18/compact-functional/code128-step3/271-coins/two-channel/v1", "functional descriptor"),
        "AV8/R17/four-image-residuals/compact-binding-v2",
        "AV8/R18/four-image-residuals/sparse-coded-v1", "image domain"))
    sparse_source = a.repo / "tools/r18_sparse_coded_g.rs"
    shutil.copy2(sparse_source, root / sparse_source.name)
    # No frame, Merkle, denominator, canonicality, image, query, or observation
    # checks are removed. Both verifiers and affine correction gates are kept.
    assert "v[441..697]" in (root / "performance.rs").read_text()
    assert "v[697..953]" in (root / "performance.rs").read_text()
    assert "r17_g_witness_audit" in (root / "performance.rs").read_text()
    assert sha(root / "r16_basis_transport.rs") == sha(a.stage / EXPERIMENTS / "r16_basis_transport.rs")
    files = {str(p.relative_to(a.output)): sha(p) for p in sorted(root.glob("*.rs"))}
    files.update({str(p.relative_to(a.output)):sha(p) for p in sorted((a.output / "crates/aspis-core/src").rglob("*.rs"))})
    metadata = dict(profile=PROFILE, base_revision=BASE, source_revision=revision,
        predecessor=str(a.stage), changes=changes, files=files,
        current_T_unchanged=True, observations=953, source_gates_passed=False,
        compact_primary=False, privacy_proved=False, soundness_proved=False,
        sbf_measured=False)
    (a.output / "r18-stage.json").write_text(json.dumps(metadata, indent=2)+"\n")
    host = json.loads((a.output / "r17-stage.json").read_text())
    host.update(profile=PROFILE, privacy_proved=False, soundness_preservation_proved=False)
    (a.output / "r17-stage.json").write_text(json.dumps(host, indent=2)+"\n")
    print(json.dumps({"stage":str(a.output),"profile":PROFILE,"source_revision":revision}))


if __name__ == "__main__":
    main()
