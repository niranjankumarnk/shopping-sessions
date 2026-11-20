# Shopping Sessions

Entry for the Builders Buildathon, Databricks track. A multi-threaded Rust
pipeline that reads the click-stream CSVs from `/data` and writes
`/output/user_daily` and `/output/campaign_daily` as Parquet.

## Run

    docker buildx build --platform linux/amd64 --load -t shopping-sessions:latest .
    scripts/docker_run.sh DATA_DIR OUTPUT_DIR

## Pre-existing code and libraries

No pre-existing repository was used. Written during the event with AI
assistance. Open-source crates: memmap2, rayon, memchr, xxhash-rust,
hashbrown, arrow-array, arrow-schema, parquet. The files in `scripts/` come
from the track's starter kit.

## License

MIT
