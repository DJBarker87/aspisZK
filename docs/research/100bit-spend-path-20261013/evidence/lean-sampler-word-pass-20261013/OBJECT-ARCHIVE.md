Compiled object bytes are retained in `compiled-objects.tar.gz`, with the
original relative filenames as archive members. Loose `.olean` files are
git-ignored and excluded from `SHA256SUMS`; extract the archive to recover
those paths. Source hashes, axiom logs and runner receipts are unchanged.
