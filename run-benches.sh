#!/bin/bash
echoerr() { echo "$@" 1>&2; }

run() {
    a="target/release/pointer-analysis -c 0 -j $@ 2> /dev/null | sed 's/^/      /'"
    timeout 1h bash -c "$a"
}

run_three() {
    run1=$(run $@)
    if [ $? -eq 0 ]; then
        run2=$(run $@)
        if [ $? -eq 0 ]; then
            run3=$(run $@)
            if [ $? -eq 0 ]; then
                echo "$run1,"
                echo "$run2,"
                echo "$run3"
            fi
        fi
    fi
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
    run_three -s tidal $bench
    echo "    ],"

    if [ "$name" != "cpython" ]; then
        echoerr "Tidal Propagation (Roaring call graph)"
        echo "    \"tidal_roaring\": ["
        run_three -s tidal -t roaring -d call-graph $bench
        echo "    ],"
    fi

    echoerr "Tidal Propagation (Call graph)"
    echo "    \"tidal_call_graph\": ["
    run_three -s tidal -d call-graph $bench
    echo "    ],"

    echoerr "Wave Propagation (Shared)"
    echo "    \"wave_shared\": ["
    run_three -s wave $bench

    if [ "$name" != "cpython" ]; then
        echo "    ],"
        echoerr "Wave Propagation (Roaring)"
        echo "    \"wave_roaring\": ["
        run_three -s wave -t roaring $bench
    fi


    if [ "$name" = "curl" ] || [ "$name" = "make" ] || [ "$name" = "htop" ]; then
        echo "    ],"

        echoerr "Demand Worklist (Hash)"
        echo "    \"demand_hash\": ["
        run_three -s basic-demand -t hash $bench
        echo "    ],"

        echoerr "Demand Worklist (Call graph)"
        echo "    \"demand_call_graph\": ["
        run_three -s basic-demand -t hash -d call-graph $bench
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