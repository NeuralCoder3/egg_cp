# cargo run --release --features='hotpath,hotpath-alloc' -- --iterations 5 --cp-count 75 --cp-retain 10 --expression-file data/own/pulse_50k.csv --suffix v125

# cargo run --release --features='hotpath,hotpath-alloc' -- --iterations 5 --cp-count 75 --cp-retain 10 --expression-file data/own/pulse_50k.csv --suffix v139 --node_limit 5000 --last_node_limit 50000
cargo run --release --features='hotpath,hotpath-alloc' -- --iterations 5 --cp-count 75 --cp-retain 10 --expression-file data/prefix/evaluation.csv --suffix v139 --node_limit 5000 --last_node_limit 50000
