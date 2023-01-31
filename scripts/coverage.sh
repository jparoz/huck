#!/usr/bin/env bash

env RUSTFLAGS="-C instrument-coverage" cargo +nightly test --tests

cargo +nightly profdata -- merge -sparse default_*.profraw -o test.profdata

cargo +nightly cov -- report \
    --use-color \
    --ignore-filename-regex='/.cargo/registry' \
    --Xdemangler=rustfilt \
    --instr-profile=test.profdata \
    --show-instantiation-summary \
    $( \
      for file in \
        $( \
          RUSTFLAGS="-C instrument-coverage" \
            cargo +nightly test --tests --no-run --message-format=json \
              | jq -r "select(.profile.test == true) | .filenames[]" \
              | grep -v dSYM - \
        ); \
      do \
        printf "%s %s " --object $file; \
      done \
    ) \
    > coverage.out

echo -e "\n\n---------------------------------------------\n\n" >> coverage.out

cargo +nightly cov -- show \
    --use-color \
    --ignore-filename-regex='/.cargo/registry' \
    --Xdemangler=rustfilt \
    --instr-profile=test.profdata \
    --show-instantiations \
    --show-line-counts-or-regions \
    $( \
      for file in \
        $( \
          RUSTFLAGS="-C instrument-coverage" \
            cargo +nightly test --tests --no-run --message-format=json \
              | jq -r "select(.profile.test == true) | .filenames[]" \
              | grep -v dSYM - \
        ); \
      do \
        printf "%s %s " --object $file; \
      done \
    ) \
    >> coverage.out

rm *.profraw test.profdata
