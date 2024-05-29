echo "Building.."
cargo build --release &> /dev/null

echo "## Tidal Propagation (Shared) ##"
cargo bench SharedBitVecTidal 2>> stderr.txt

echo "## Tidal Propagation (Roaring) ##"
cargo bench RoaringTidal 2>> stderr.txt

echo "## Wave Propagation (Shared) ##"
cargo bench SharedBitVecWave 2>> stderr.txt

echo "## Wave Propagation (Roaring) ##"
cargo bench RoaringWave 2>> stderr.txt

echo "## Demand Worklist (Hash) ##"
cargo bench BasicDemand 2>> stderr.txt