FROM --platform=linux/amd64 ubuntu:24.04
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends python3 ca-certificates libudev1 libcap2 && rm -rf /var/lib/apt/lists/*
COPY cli /opt/aspis/cli
COPY devnet_spend /opt/aspis/devnet_spend
ENV NO_DNA=1
