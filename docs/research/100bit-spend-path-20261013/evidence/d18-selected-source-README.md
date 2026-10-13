# D18 selected source archive

Archive: [`d18-selected-source.tar`](d18-selected-source.tar)

- SHA-256: `03dcf08d418d18ebe2b83e8bf7aec2cd07f8179144e173131fe9d03f158e092d`
- Source-manifest path: `evidence/latest/results/100bit-path-20261013/d18/source-manifest.json`
- Selected source files: 368, taken only from the manifest's explicit `files` map
- Archive members: 368 source files plus `source-manifest.json` (369 regular-file members; directory entries are implicit)
- Manifest schema: `aspis.100bit-path.actual-source-sha256.v1`
- Manifest file-set SHA-256: `f75e70d832444fd562d3ffb000f37e2f0b1c06f7940a2334f04457011e17e8be`
- Raw source-manifest SHA-256: `6558dd09891bfe78db3165d19ff84805c3f8416e9e235898095db35c942d2a17`
- Source revision: `7742957648c33cf045eb6a672e7c7cc796b61087+d18+f75e70d832444fd562d3ffb000f37e2f0b1c06f7940a2334f04457011e17e8be`

Each manifest-listed path was checked against its SHA-256 before archive creation.
The manifest's canonical file-map hash and source-revision suffix were also
checked. The archive contains `source-manifest.json` at its root and each listed
repository file under `source/<repository-relative-path>`. After extracting to
a temporary directory, the manifest bytes and parsed contents matched the
original, and all 368 extracted files matched the manifest hashes.

The archive was written as an uncompressed GNU tar with sorted member names,
zeroed timestamps and owner IDs/names, and the source files' permission bits.
It contains only those explicit manifest-listed files and the manifest; it does
not include keys, build outputs, ELF files, fixtures, or unrelated evidence.
