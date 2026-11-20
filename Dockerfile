# Shopping Sessions: multi-threaded Rust pipeline.
# The scorer builds this natively on linux/amd64.
FROM rust:1-slim-bookworm AS build
WORKDIR /src
COPY Cargo.toml Cargo.lock ./
COPY src ./src
RUN cargo build --release --locked

FROM debian:bookworm-slim
COPY --from=build /src/target/release/shopping /app/shopping
# Runs as uid 1000 with a read-only root; only /output and /scratch are writable.
ENV DATA_DIR=/data OUTPUT_DIR=/output SCRATCH_DIR=/scratch
CMD ["/app/shopping"]
