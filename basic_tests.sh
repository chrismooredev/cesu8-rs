
# exit the script if any command failes
# eg) building, comparing differing files
set -e

echo "running tests, will state if successful - will exit on failure"

cargo build --bin cesu8 --features build-binary

cargo test

echo "testing group (random.txt)..."

echo "xxd -r random.txt.xxd"
cmp --quiet random.txt <(xxd -r random.txt.xxd)

echo "cesu8 --decode random.cesu8.txt"
cmp --quiet random.txt <(./target/debug/cesu8 --decode random.cesu8.txt)

echo "testing group random.cesu8.txt"

echo "xxd -r random.cesu8.txt.xxd"
cmp --quiet random.cesu8.txt <(xxd -r random.cesu8.txt.xxd)

echo "cesu8 random.txt"
cmp --quiet random.cesu8.txt <(./target/debug/cesu8 random.txt)

echo "round trip `cesu8 random.txt | cesu8 --decode`"
cmp --quiet random.txt <(./target/debug/cesu8 random.txt | ./target/debug/cesu8 --decode)

echo "all tests successful"
