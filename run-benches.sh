#!/bin/bash
echoerr() { echo "$@" 1>&2; }

run() {
    target/release/pointer-analysis $1 -c 0 -j $2 2> /dev/null | sed 's/^/      /'
}

echoerr "Building.."
cargo build --release > /dev/null 2>&1

declare -a benches
benches=(benchmarks/*/bench.bc)
# benches=(benchmarks/curl/bench.bc benchmarks/make/bench.bc benchmarks/htop/bench.bc)

echo "{"
for bench in "${benches[@]}"; do
    name=${bench#"benchmarks/"}
    name=${name%"/bench.bc"}

    echoerr "#### ${name} ####"
    echo "  \"$name\": {"

    echoerr "Tidal Propagation (Shared)"
    echo "    \"tidal_shared\": ["
    echo "$(run "-s tidal" $bench),"
    echo "$(run "-s tidal" $bench),"
    echo "$(run "-s tidal" $bench)"
    echo "    ],"

    echoerr "Tidal Propagation (Roaring)"
    echo "    \"tidal_roaring\": ["
    echo "$(run "-s tidal -t roaring" $bench),"
    echo "$(run "-s tidal -t roaring" $bench),"
    echo "$(run "-s tidal -t roaring" $bench)"
    echo "    ],"

    echoerr "Tidal Propagation (Call graph)"
    echo "    \"tidal_call_graph\": ["
    echo "$(run "-s tidal -d call-graph" $bench),"
    echo "$(run "-s tidal -d call-graph" $bench),"
    echo "$(run "-s tidal -d call-graph" $bench)"
    echo "    ],"

    echoerr "Wave Propagation (Shared)"
    echo "    \"wave_shared\": ["
    echo "$(run "-s wave" $bench),"
    echo "$(run "-s wave" $bench),"
    echo "$(run "-s wave" $bench)"
    echo "    ],"

    echoerr "Wave Propagation (Roaring)"
    echo "    \"wave_roaring\": ["
    echo "$(run "-s wave -t roaring" $bench),"
    echo "$(run "-s wave -t roaring" $bench),"
    echo "$(run "-s wave -t roaring" $bench)"

    if [ "$name" = "curl" ] || [ "$name" = "make" ] || [ "$name" = "htop" ]; then
        echo "    ],"

        echoerr "Demand Worklist (Hash)"
        echo "    \"demand_hash\": ["
        echo "$(run "-s basic-demand -t hash -d call-graph" $bench),"
        echo "$(run "-s basic-demand -t hash -d call-graph" $bench),"
        echo "$(run "-s basic-demand -t hash -d call-graph" $bench)"
        echo "    ],"

        echoerr "Demand Worklist (Call graph)"
        echo "    \"demand_call_graph\": ["
        echo "$(run "-s basic-demand -t hash" $bench),"
        echo "$(run "-s basic-demand -t hash" $bench),"
        echo "$(run "-s basic-demand -t hash" $bench)"
        echo "    ]"
    else
        echo "    ]"
    fi

    if [ "$bench" = ${benches[-1]} ]; then
        echo "  }"
    else
        echo "  },"
    fi
done
echo "}"