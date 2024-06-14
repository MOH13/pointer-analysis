#!/usr/bin/env python3

import json
import sys
import os
from typing import Callable
from matplotlib.colors import LinearSegmentedColormap, ListedColormap
from matplotlib import colormaps
import matplotlib.pyplot as plt
import numpy as np

if len(sys.argv) != 2:
    print("Please provide a prefix!")
    print("usage: ./make-tables.py [prefix] < [file.json]")
    exit(1)

prefix = sys.argv[1]

os.makedirs("./table_output", exist_ok=True)


def convert_to_str(values: iter, col):
    if col.endswith("_ms"):
        return f"{(min(values) / 1000):.3f}"
    elif col.startswith("mean_"):
        return f"{next(values):.2f}"
    elif col == "memory":
        return f"{(min(values) / 1024 / 1024):.2f}"
    return str(next(values))


def get_path(file: str):
    return f"table_output/{prefix}_{file}"


def make_table(
    data: dict[str, dict[str, list[dict]]],
    file: str,
    solvers: list[str],
    solver_names: list[str],
    cols: list[str],
    col_names: list[str],
):
    with open(get_path(file), "w") as my_file:

        def print_to_file(text: str, end: str = "\n"):
            print(text, file=my_file, end=end)

        cols_alignment = "r" * len(solvers) * len(cols)
        cols_str = " & ".join(
            [
                f"\\multicolumn{{{len(solvers)}}}{{c}}{{{col_name}}}"
                for col_name in col_names
            ]
        )
        cols_midrule = "".join(
            [
                f"\\cmidrule(lr){{{i*len(solvers)+2}-{(i+1)*len(solvers)+1}}}"
                for i in range(len(cols))
            ]
        )
        solvers_str = " & ".join(solver_names * len(cols))

        print_to_file(f"\\begin{{tabular}}{{@{{}}l{cols_alignment}@{{}}}}")
        print_to_file("    \\toprule")
        print_to_file(f"    & {cols_str} \\\\")
        if len(solvers) > 1:
            print_to_file(f"    {cols_midrule}")
            print_to_file(f"    & {solvers_str} \\\\")
        print_to_file("    \\hline")
        for test, solver_runs in data.items():
            print_to_file(f"    \\texttt{{{test}}} & ", end="")
            solver_strs = [[] for _ in cols]
            for solver in solvers:
                if solver not in solver_runs:
                    for i in range(len(cols)):
                        solver_strs[i].append("DNR")
                    continue
                if "error" in solver_runs[solver][0]:
                    for i in range(len(cols)):
                        solver_strs[i].append(solver_runs[solver][0]["error"])
                    continue
                runs = solver_runs[solver]
                extract_value = lambda col: (
                    convert_to_str(map(lambda run: run[col], runs), col)
                    if col in runs[0]
                    else "DNR"
                )
                values = map(extract_value, cols)
                for i, value in enumerate(values):
                    solver_strs[i].append(value)
            print_to_file(
                f"{' & '.join(map(lambda col_strs: ' & '.join(col_strs), solver_strs))} \\\\",
            )
        print_to_file("    \\bottomrule")
        print_to_file("\\end{tabular}")


def get_data_for_solver(
    data: dict[str, dict[str, list[dict]]],
    solver: str,
    cols: list[str | Callable[[dict], int]],
    min_key=None,
):
    if min_key == None:
        min_key = "solver_time_ms"

    def col_to_res(run, col):
        if callable(col):
            return col(run)
        return run[col]

    runs_per_prog = map(lambda solver_runs: solver_runs[solver], data.values())

    min_run_per_prog = map(
        lambda runs: min(runs, key=lambda run: run[min_key]), runs_per_prog
    )

    return np.array(
        [np.array([col_to_res(run, col) for col in cols]) for run in min_run_per_prog]
    )


def lighten_color(color, amount=0.5):
    """
    Lightens the given color by multiplying (1-luminosity) by the given amount.
    Input can be matplotlib color string, hex string, or RGB tuple.

    Examples:
    >> lighten_color('g', 0.3)
    >> lighten_color('#F034A3', 0.6)
    >> lighten_color((.3,.55,.1), 0.5)
    """
    import matplotlib.colors as mc
    import colorsys

    try:
        c = mc.cnames[color]
    except:
        c = color
    c = colorsys.rgb_to_hls(*mc.to_rgb(c))
    return colorsys.hls_to_rgb(c[0], 1 - amount * (1 - c[1]), c[2])


data: dict[str, dict[str, list[dict]]] = json.load(sys.stdin)

for test, solver_runs in data.items():
    for solver, runs in solver_runs.items():
        if "tidal" not in solver and "wave" not in solver:
            continue
        for run in runs:
            if "error" in run:
                continue
            run["init_time_ms"] = (
                run["solver_time_ms"]
                - run["dedup_time_ms"]
                - run["scc_time_ms"]
                - run["term_propagation_time_ms"]
                - run["edge_instantiation_time_ms"]
            )
            if "query_propagation_time_ms" in run:
                run["init_time_ms"] -= run["query_propagation_time_ms"]
            if "num_segments" in run:
                run["saving_mb"] = (
                    (run["num_segments"] - run["num_chunks"]) * 24 * 8 // 1024 // 1024
                )

make_table(
    data,
    "program_stats.tex",
    ["stats"],
    [""],
    [
        "terms",
        "inclusions",
        "subsets",
        # "offset_subsets",
        "loads",
        # "offset_loads",
        "stores",
        # "offset_stores",
        # "total"
    ],
    [
        "Terms",
        "Addr. ofs",
        "Assignments",
        # "Offset Assignments",
        "Loads",
        # "Offset Loads",
        "Stores",
        # "Offset Stores",
        # "Total"
    ],
)

make_table(
    data,
    "time.tex",
    ["tidal_shared", "tidal_call_graph", "wave_shared", "demand_call_graph"],
    ["TP (All)", "TP (CG)", "WP", "WL"],
    ["solver_time_ms", "memory"],
    ["Time (s)", "Memory (MB)"],
)

make_table(
    data,
    "term_sets.tex",
    ["tidal_call_graph", "tidal_non_aggressive", "tidal_roaring"],
    ["Fully Shared", "Chunks Only", "Roaring"],
    ["solver_time_ms", "memory"],
    ["Time (s)", "Memory (MB)"],
)

make_table(
    data,
    "call_stats.tex",
    ["tidal_shared"],
    [""],
    [
        "num_called_functions",
        "num_called_non_trivial_functions",
        "mean_call_edges",
        "mean_non_trivial_call_edges",
    ],
    [
        "\\#Called",
        "\\#Called (NT)",
        "Mean Call Edges",
        "Mean Call Edges (NT)",
    ],
)

make_table(
    data,
    "scc_and_iterations.tex",
    ["tidal_shared", "tidal_call_graph"],
    ["TP (All)", "TP (CG)"],
    ["non_empty_nodes", "sccs", "iterations"],
    ["\\# Non-empty", "\\# SCCs", "\\# Iterations"],
)


def make_chunk_sharing_table(solver: str, file: str):
    make_table(
        data,
        file,
        [solver],
        ["---"],
        [
            "total_term_sets",
            "unique_sets",
            "num_segments",
            "num_chunks",
            "num_unique_chunks",
            "saving_mb",
        ],
        [
            "\\#Sets",
            "\\#Uniq. Sets",
            "\\#Segments",
            "\\#Chunks",
            "\\#Uniq. Chunks",
            "Saving (MB)",
        ],
    )


def make_full_sharing_table(solver: str, file: str):
    make_table(
        data,
        file,
        [solver],
        ["---"],
        [
            "total_term_sets",
            "unique_sets",
            "num_segments",
            "num_chunks",
            "num_unique_chunks",
        ],
        [
            "\\#Sets",
            "\\#Uniq. Sets",
            "\\#Segments",
            "\\#Chunks",
            "\\#Uniq. Chunks",
        ],
    )


make_chunk_sharing_table("tidal_non_aggressive", "sharing_chunk_tidal.tex")

make_full_sharing_table("tidal_shared", "sharing_full_tidal.tex")
make_full_sharing_table("tidal_call_graph", "sharing_tidal_call_graph.tex")

programs = list(data.keys())
solvers = {
    "TP (All)": get_data_for_solver(
        data,
        "tidal_shared",
        [
            "init_time_ms",
            "scc_time_ms",
            "term_propagation_time_ms",
            "edge_instantiation_time_ms",
            "dedup_time_ms",
            "query_propagation_time_ms",
        ],
    ),
    "TP (CG)": get_data_for_solver(
        data,
        "tidal_call_graph",
        [
            "init_time_ms",
            "scc_time_ms",
            "term_propagation_time_ms",
            "edge_instantiation_time_ms",
            "dedup_time_ms",
            "query_propagation_time_ms",
        ],
    ),
    "WP": get_data_for_solver(
        data,
        "wave_shared",
        [
            "init_time_ms",
            "scc_time_ms",
            "term_propagation_time_ms",
            "edge_instantiation_time_ms",
            "dedup_time_ms",
        ],
    ),
}
labels = {
    "TP (All)": ["Init", "SCC", "TermProp", "EdgeInst", "Dedup", "QueryProp"],
    "TP (CG)": ["Init", "SCC", "TermProp", "EdgeInst", "Dedup", "QueryProp"],
    "WP": ["Init", "SCC", "TermProp", "EdgeInst", "Dedup"],
}

x = np.arange(len(programs))
width = 0.25  # the width of the bars
multiplier = 0

color_map = colormaps.get_cmap("Set2")
steps = 8
color_maps = {
    "TP (All)": ListedColormap(
        [lighten_color(color_map(i / steps), 1.3) for i in range(steps)]
    ),  # LinearSegmentedColormap.from_list("",['#1D2671', '#C33764', '#f7411d']),
    "TP (CG)": ListedColormap(
        [lighten_color(color_map(i / steps), 1.1) for i in range(steps)]
    ),  ##LinearSegmentedColormap.from_list("",['green','yellow']),
    "WP": ListedColormap(
        [lighten_color(color_map(i / steps), 0.9) for i in range(steps)]
    ),  # LinearSegmentedColormap.from_list("",['red','white']),
}

color_steps = {
    "TP (All)": 1 / steps,
    "TP (CG)": 1 / steps,
    "WP": 1 / steps,
}

bottoms = {solver: np.zeros(len(programs), dtype=np.float64) for solver in solvers}

program_wp_times = np.array([np.sum(solvers["WP"][i]) for i in range(len(programs))])
program_norms = 1 / program_wp_times

plt.rcParams.update({"text.usetex": True})
fig, ax = plt.subplots(layout="constrained")

for solver, values in solvers.items():
    offset = width * multiplier
    for i, vals in enumerate(np.transpose(values)):
        scaled_vals = vals * program_norms
        color_idx = i * color_steps[solver]
        if solver == "WP" and i == 4:
            rects = ax.bar(
                x + offset,
                scaled_vals,
                width,
                bottom=bottoms[solver],
                label=f"{solver} {labels[solver][i]}",
                color=color_maps[solver](color_idx),
            )
            ax.bar_label(rects, [f"{t/1000:.2f}s" for t in program_wp_times], padding=3)
        else:
            ax.bar(
                x + offset,
                scaled_vals,
                width,
                bottom=bottoms[solver],
                label=f"{solver} {labels[solver][i]}",
                color=color_maps[solver](color_idx),
            )
        bottoms[solver] += scaled_vals
    multiplier += 1

ax.set_xticks(x + width, programs, verticalalignment="baseline")
ax.tick_params(axis="x", pad=10)
ax.legend(loc="upper right", ncols=len(solvers), fontsize="small")
ax.set_ylim(0, 2)


# Plot over reduction in non-empty vs speedup
# fig, ax = plt.subplots(layout='constrained')

# all_data = get_data_for_solver(data, "tidal_shared", ["non_empty_nodes", "solver_time_ms"])
# cg_data = get_data_for_solver(data, "tidal_call_graph", ["non_empty_nodes", "solver_time_ms"])

# x = [(a-c)/a for (a, c) in zip(all_data[:,0], cg_data[:,0])]
# y = [(a-c)/a for (a, c) in zip(all_data[:,1], cg_data[:,1])]

# ax.set_xlim(0, 1)
# ax.set_ylim(0, 1)
# ax.plot(x, y, 'o')

plt.savefig(get_path("relative_times_graph.pgf"))
plt.savefig(get_path("relative_times_graph.pdf"))
plt.show()
