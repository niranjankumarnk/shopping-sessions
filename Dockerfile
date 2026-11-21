# Shopping Sessions: multi-threaded Rust pipeline, built as one static binary.
# The scorer builds this natively on linux/amd64. Both images are pinned by digest because the
# final rebuilds every entry after the cutoff.
FROM rust:1.100.0-slim-bookworm@sha256:7c7d4eb4d05b7781187a327809466cfddf29753f6defdc3d19a0e291951b7a37 AS build
WORKDIR /src
COPY Cargo.toml Cargo.lock ./
COPY src ./src
# The target is spelled out so that the static-linking flag reaches only our own code.
RUN target="$(rustc -vV | sed -n 's/^host: //p')" \
 && RUSTFLAGS="-C target-feature=+crt-static" cargo build --release --locked --target "$target" \
 && cp "target/$target/release/shopping" /shopping

FROM busybox:1.36.1-glibc@sha256:7e567dff0fbaa48cddc5f52ae5201a7f417436aa20e70c8750814692043dfa38
COPY --from=build /shopping /app/shopping
# Runs as uid 1000 with a read-only root; only /output and /scratch are writable.
# GLIBC_TUNABLES: back the heap with huge pages on hosts that give them only on request.
ENV DATA_DIR=/data OUTPUT_DIR=/output SCRATCH_DIR=/scratch GLIBC_TUNABLES=glibc.malloc.hugetlb=1
CMD ["/app/shopping"]
