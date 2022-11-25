#!/bin/bash

set -e

# TODO: convert this to proper tests within cesu8str (move count_codepoints logic into main codebase?)

echo "building..."
cargo build --release --bin count_codepoints --quiet 2>/dev/null

# the debug mode has some extra checks enabled that release mode skips, so run these tests in debug mode
cargo build --bin cesu8str --features "build-binary" --quiet 2>/dev/null

echo "following hashes should be the same..."
./target/debug/cesu8str test_files/random.txt 2>/dev/null | md5sum test_files/random.cesu8.txt /dev/stdin

as_refer="$(./target/release/count_codepoints --json test_files/random.txt)"
as_cesu8="$(./target/release/count_codepoints --json test_files/random.cesu8.txt)"
combined="{ \"reference\": $as_refer, \"processed\": $as_cesu8 }"

echo -n "utf8(4len)*2 + utf8(3len) == cesu8(3len) :: "
jq '.reference.len3+.reference.len4*2 == .processed.len3' <<< "$combined"
