#!/bin/bash
echoerr() { echo "$@" 1>&2; }

run() {
    a="target/release/pointer-analysis -j $@ > /tmp/pointer-data.json"
    stats="$(runexec --walltimelimit 3600 --memlimit 21474836480 --no-container -- bash -c "$a")"
    terminationreason="$(grep -oP '(?<=\bterminationreason=)[^;]+' <<< "$stats")"
    if [ $? -eq 0 ]; then
        echoerr "Termination reason: $terminationreason"
        if [ "$terminationreason" = "walltime" ]; then
            echo '      { "error": "DNF" }'
            echoerr "Walltime exceeded"
            return 5
        elif [ "$terminationreason" = "memory" ]; then
            echo '      { "error": "OOM" }'
            echoerr "Memory exceeded"
            return 6
        else
            echo '      { "error": "'"$terminationreason"'" }'
            echoerr "Unknown termination reason"
            return 42
        fi
    fi
    memory="$(grep -oP '(?<=\bmemory=)[^;]+' <<< "$stats")"
    jq < /tmp/pointer-data.json '. += {"memory": '"${memory%B}"'}' | sed 's/^/      /'
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
            else
                echo "$run3"
            fi
        else
            echo "$run2"
        fi
    else
        echo "$run1"
    fi
}

if [ $# -eq 0 ]; then
    echoerr "Usage: $0 -c 0 or $0 -c 1"
    exit 1
fi

echoerr "Building.."
cargo build --release > /dev/null

if [ $? -ne 0 ]; then
    echoerr "Build failed"
    exit 1
fi

declare -a benches
benches=(benchmarks/*/bench.bc)
# benches=(benchmarks/curl/bench.bc benchmarks/make/bench.bc)

echo "{"
for bench in "${benches[@]}"; do
    name=${bench#"benchmarks/"}
    name=${name%"/bench.bc"}

    echoerr "#### ${name} ####"
    echo "  \"$name\": {"
    
    echo "    \"stats\": ["
    target/release/pointer-analysis -s dry-run -j $bench 2> /dev/null | sed 's/^/      /'
    echo "    ],"

    echoerr "Tidal Propagation (Shared)"
    echo "    \"tidal_shared\": ["
    run_three $@ -s tidal -a $bench
    echo "    ],"

    echoerr "Tidal Propagation (Roaring call graph)"
    echo "    \"tidal_roaring\": ["
    run_three $@ -s tidal -t roaring -d call-graph -g non-trivial -a $bench
    echo "    ],"

    echoerr "Tidal Propagation (Call graph)"
    echo "    \"tidal_call_graph\": ["
    run_three $@ -s tidal -d call-graph -g non-trivial -a $bench
    echo "    ],"

    echoerr "Tidal Propagation (Call graph, non-aggressive)"
    echo "    \"tidal_non_aggressive\": ["
    run_three $@ -s tidal -d call-graph -g non-trivial $bench
    echo "    ],"

    echoerr "Wave Propagation (Shared)"
    echo "    \"wave_shared\": ["
    run_three $@ -s wave -a $bench
    echo "    ],"

    # echoerr "Wave Propagation (Roaring)"
    # echo "    \"wave_roaring\": ["
    # run_three $@ -s wave -t roaring -a $bench
    # echo "    ],"

    # echoerr "Demand Worklist (Hash)"
    # echo "    \"demand_hash\": ["
    # run_three $@ -s basic-demand -t hash $bench
    # echo "    ],"

    echoerr "Demand Worklist (Call graph)"
    echo "    \"demand_call_graph\": ["
    run_three $@ -s basic-demand -t hash -d call-graph -g non-trivial $bench
    echo "    ]"

    if [ "$bench" = ${benches[-1]} ]; then
        echo "  }"
    else
        echo "  },"
    fi
done
echo "}"