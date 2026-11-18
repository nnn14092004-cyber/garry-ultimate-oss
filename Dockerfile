# ==============================================================================
# Stage 1: Deterministic Pure-Rust Builder (Zero External Crates, v3.0.0)
# ==============================================================================
FROM rust:1.82-slim-bookworm AS builder

WORKDIR /usr/src/garry-ultimate-oss

COPY Cargo.toml LICENSE README.md ROADMAP.md ./
COPY src ./src
COPY docs ./docs
COPY paper ./paper

RUN cargo clippy --all-targets -- -D warnings && \
    cargo test --release && \
    cargo build --release --locked

# ==============================================================================
# Stage 2: Minimal Air-Gapped 10-Pillar & Navier-Stokes Millennium Sandbox
# ==============================================================================
FROM debian:bookworm-slim

WORKDIR /app

RUN useradd -m -u 10001 garry && \
    mkdir -p /app/garry_workspace/knowledge \
             /app/garry_workspace/scripts \
             /app/garry_workspace/solutions && \
    chown -R garry:garry /app

COPY --from=builder /usr/src/garry-ultimate-oss/target/release/garry-ultimate-oss /usr/local/bin/garry-ultimate-oss
COPY --from=builder /usr/src/garry-ultimate-oss/README.md /app/README.md
COPY --from=builder /usr/src/garry-ultimate-oss/ROADMAP.md /app/ROADMAP.md
COPY --from=builder /usr/src/garry-ultimate-oss/LICENSE /app/LICENSE

USER garry

ENTRYPOINT ["/usr/local/bin/garry-ultimate-oss"]