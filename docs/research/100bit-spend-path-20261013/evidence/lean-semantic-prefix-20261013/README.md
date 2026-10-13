# Restoring target objects

`target-objects.tar.gz` contains the 14 selected final target `.olean` files only; external dependency objects are not included. Extract it at the root of the chosen object overlay, preserving the `objects/` prefix. For example:

```sh
mkdir -p /path/to/lean-overlay
tar -xzf target-objects.tar.gz -C /path/to/lean-overlay
```

Use the matching pinned Mathlib/Aspis dependency cache from the recorded workspace separately. The per-attempt logs and source snapshots are evidence inputs, not a standalone Lean build environment. `manifest.json` gives the object members and all attempt/source/resource/axiom details. Verify files with `sha256sum -c SHA256SUMS` from this directory.
