# Future-version one-transaction devnet client: the PIN2 writer image with the devnet_spend
# binary built on the build host from branch future-version (features r1p-check).
FROM aspis-pin2-writer:20261111
COPY devnet_spend /opt/aspis/devnet_spend
RUN chmod 0755 /opt/aspis/devnet_spend
ENV NO_DNA=1
