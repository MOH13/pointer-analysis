#!/usr/bin/env python3

import json
import sys
import matplotlib.pyplot as plt
import numpy as np

def convert_to_str(values: iter, col):
    if col.endswith('_ms'):
        return f"{(min(values) / 1000):.3f}"
    elif col.startswith('mean_'):
        return f"{next(values):.2f}"
    elif col == 'memory':
        return f"{(min(values) / 1024 / 1024):.2f}"
    return str(next(values))

def make_table(data: dict[str, dict[str, list[dict]]], solvers: list[str], solver_names: list[str], cols: list[str], col_names: list[str]):
    cols_alignment = "c"*len(solvers)*len(cols)
    cols_str = " & ".join([f"\\multicolumn{{{len(solvers)}}}{{c}}{{{col_name}}}" for col_name in col_names])
    cols_midrule = "".join([f"\\cmidrule(lr){{{i*len(solvers)+2}-{(i+1)*len(solvers)+1}}}" for i in range(len(cols))])
    solvers_str = " & ".join(solver_names * len(cols))

    print(f"\\begin{{tabular}}{{@{{}}l{cols_alignment}@{{}}}}")
    print("    \\toprule")
    print(f"    & {cols_str} \\\\")
    if len(solvers) > 1:
        print(f"    {cols_midrule}")
        print(f"    & {solvers_str} \\\\")
    print("    \\hline")
    for test, solver_runs in data.items():
        print(f"    \\texttt{{{test}}} & ", end="")
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
            extract_value = lambda col: convert_to_str(map(lambda run: run[col], runs), col) if col in runs[0] else "DNR"
            values = map(extract_value, cols)
            for i, value in enumerate(values):
                solver_strs[i].append(value)
        print(f"{' & '.join(map(lambda col_strs: ' & '.join(col_strs), solver_strs))} \\\\",)
    print("    \\bottomrule")
    print("\\end{tabular}")

def get_data_for_solver(data: dict[str, dict[str, list[dict]]], solver: str, cols: list[str]):
    runs_per_prog = map(lambda solver_runs: solver_runs[solver], data.values())
    return np.array([np.array([min(map(lambda run: run[col], runs)) for col in cols]) for runs in runs_per_prog])

data: dict[str, dict[str, list[dict]]] = json.load(sys.stdin)

["terms",
        "inclusions",
        "subsets",
        "offset_subsets",
        "loads",
        "offset_loads",       "stores",
        "offset_stores",
        "total"]

make_table(data, ["stats"], [""], [
        "terms",
        "inclusions",
        "subsets",
        # "offset_subsets",
        "loads",
        # "offset_loads",
        "stores",
        # "offset_stores",
        # "total"
    ], [
        "Terms",
        "Addr. ofs",
        "Assignments",
        # "Offset Assignments",
        "Loads",
        # "Offset Loads",
        "Stores",
        # "Offset Stores",
        # "Total"
    ])
make_table(data, ["tidal_shared", "tidal_call_graph", "wave_shared", "demand_hash", "demand_call_graph"], ["TP (All)", "TP (CG)", "WP", "WL (All)", "WL (CG)"], ["solver_time_ms"], ["Time (s)"])
make_table(data, ["tidal_call_graph", "tidal_roaring"], ["TP (Shared)", "TP (Roaring)"], ["solver_time_ms", "memory"], ["Time (s)", "Memory (MB)"])
make_table(data, ["tidal_shared"], [""], ["num_called_functions", "num_called_non_trivial_functions", "mean_call_edges", "mean_non_trivial_call_edges"], ["\\# Called", "\\# Called (non-trivial)", "Mean Call Edges", "Mean Call Edges (non-trivial)"])
make_table(data, ["tidal_shared", "tidal_call_graph"], ["TP (All)", "TP (CG)"], ["non_empty_nodes", "sccs", "iterations"], ["\\# Non-empty", "\\# SCCs", "\\# Iterations"])

programs = list(data.keys())
solvers = {
    "TP (All)": get_data_for_solver(data, "tidal_shared", ["scc_time_ms", "query_propagation_time_ms", "term_propagation_time_ms", "edge_instantiation_time_ms"]),
    "TP (CG)": get_data_for_solver(data, "tidal_call_graph", ["scc_time_ms", "query_propagation_time_ms", "term_propagation_time_ms", "edge_instantiation_time_ms"]),
    "WP": get_data_for_solver(data, "wave_shared", ["scc_time_ms", "term_propagation_time_ms", "edge_instantiation_time_ms"]),
}
labels = {
    "TP (All)": ["SCC", "QueryProp", "TermProp", "EdgeInst"],
    "TP (CG)": ["SCC", "QueryProp", "TermProp", "EdgeInst"],
    "WP": ["SCC", "TermProp", "EdgeInst"],
}

x = np.arange(len(programs))
width = 0.25  # the width of the bars
multiplier = 0
bottoms = {solver: np.zeros(len(programs), dtype=np.float64) for solver in solvers}

program_norms = np.array([1/np.sum(solvers["WP"][i]) for i in range(len(programs))])

fig, ax = plt.subplots(layout='constrained')

for solver, values in solvers.items():
    offset = width * multiplier
    for i, vals in enumerate(np.transpose(values)):
        scaled_vals = vals * program_norms
        rects = ax.bar(x + offset, scaled_vals, width, bottom=bottoms[solver], label=f"{solver} {labels[solver][i]}")
        # ax.bar_label(rects, padding=3)
        bottoms[solver] += scaled_vals
    multiplier += 1

ax.set_title('Running time distributions')
ax.set_xticks(x + width, programs)
ax.legend(loc='upper right', ncols=len(solvers))
ax.set_ylim(0, 2)

plt.show()
