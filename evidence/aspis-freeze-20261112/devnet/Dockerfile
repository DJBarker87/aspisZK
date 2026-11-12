# Aspis freeze devnet client: the PIN2 writer image (Solana CLI, Python) with the devnet_spend
# binary built on the build host from the frozen source (features r1p-check, host Rust 1.94.1).
FROM aspis-pin2-writer:20261111
COPY devnet_spend /opt/aspis/devnet_spend
RUN chmod 0755 /opt/aspis/devnet_spend
ENV NO_DNA=1
