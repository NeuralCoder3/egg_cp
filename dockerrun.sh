# # docker build -t neuralcoder/caviar-runner .

# # docker run --rm --init -v $(pwd)/results:/app/results -v $(pwd)/tmp:/app/tmp -v $(pwd)/data:/app/data neuralcoder/caviar_iter:v2 \
# # /bin/bash -c "cd /app; export RUST_BACKTRACE=full; \
# # export SUFFIX=_v1000; \
# # cargo run --release --features=hotpath,hotpath-alloc pulses data/own/pulse_50k.csv 1000 5000 10 2 2>&1 | tee results/pulse\$SUFFIX.txt; \
# # mv tmp/results_beh_2.csv tmp/results_beh_2_\$SUFFIX.csv;mv tmp/cp_rules.txt tmp/cp_rules\$SUFFIX.txt;mv tmp/applied_rules.txt tmp/applied_rules\$SUFFIX.txt"


# write to
# /home/s8maullr/caviar_iter/

# # cd /app; export RUST_BACKTRACE=full; export SUFFIX=_v1000; cargo run --release --features=hotpath,hotpath-alloc pulses /app/data/own/pulse_50k.csv 1000 5000 10 2 2>&1 | tee /home/s8maullr/caviar_iter/results/pulse$SUFFIX.txt; mv /home/s8maullr/caviar_iter/tmp/results_beh_2.csv /home/s8maullr/caviar_iter/tmp/results_beh_2_$SUFFIX.csv;mv /home/s8maullr/caviar_iter/tmp/cp_rules.txt /home/s8maullr/caviar_iter/tmp/cp_rules$SUFFIX.txt;mv /home/s8maullr/caviar_iter/tmp/applied_rules.txt /home/s8maullr/caviar_iter/tmp/applied_rules$SUFFIX.txt


# docker run --rm --init -v $(pwd):/home/s8maullr/caviar_iter -v $(pwd)/data:/app/data neuralcoder/caviar_iter:v3 \
# /bin/bash -c \
# 'cd /app; export RUST_BACKTRACE=full; export SUFFIX=_v1000; /app/target/release/caviar pulses /app/data/own/pulse_50k.csv 1000 5000 10 2 2>&1 | tee /home/s8maullr/caviar_iter/results/pulse$SUFFIX.txt; mv /home/s8maullr/caviar_iter/tmp/results_beh_2.csv /home/s8maullr/caviar_iter/tmp/results_beh_2_$SUFFIX.csv;mv /home/s8maullr/caviar_iter/tmp/cp_rules.txt /home/s8maullr/caviar_iter/tmp/cp_rules$SUFFIX.txt;mv /home/s8maullr/caviar_iter/tmp/applied_rules.txt /home/s8maullr/caviar_iter/tmp/applied_rules$SUFFIX.txt'

