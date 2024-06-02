#!/usr/bin/env python3

import json
import sys

def convert_to_str(values: iter, col):
    if col.endswith('_ms'):
        return f"{(min(values) / 1000):.3f}"
    elif col.startswith('mean_'):
        return f"{next(values):.2f}"
    return str(next(values))

def make_table(data: dict[str, dict[str, list[dict]]], solvers: list[str], solver_names: list[str], cols: list[str], col_names: list[str]):
    cols_alignment = "c"*len(solvers)*len(cols)
    cols_str = " & ".join([f"\\multicolumn{{{len(solvers)}}}{{c}}{{{col_name}}}" for col_name in col_names])
    cols_midrule = " & ".join([f"\\cmidrule(lr){{{i*len(solvers)+2}-{(i+1)*len(solvers)+1}}}" for i in range(len(cols))])
    solvers_str = " & ".join(solver_names)

    print(f"\\begin{{tabular}}{{@{{}}l{cols_alignment}@{{}}}}")
    print("    \\toprule")
    print(f"    & {cols_str} \\\\")
    if len(solvers) > 1:
        print(f"    {cols_midrule}")
        print(f"    & {solvers_str} \\\\")
    print("    \\hline")
    for test, solver_runs in data.items():
        print(f"    \\texttt{{{test}}} & ", end="")
        solver_strs = []
        for solver in solvers:
            if solver not in solver_runs:
                solver_strs.append(" & ".join(["DNF" for _ in cols]))
                continue
            runs = solver_runs[solver]
            extract_value = lambda col: convert_to_str(map(lambda run: run[col], runs), col) if col in runs[0] else "DNF"
            values = map(extract_value, cols)
            solver_strs.append(" & ".join(values))
        print(f"{' & '.join(solver_strs)} \\\\",)
    print("    \\bottomrule")
    print("\\end{tabular}")

data = json.load(sys.stdin)

make_table(data, ["tidal_shared", "tidal_call_graph", "wave_shared", "demand_hash", "demand_call_graph"], ["TP (All)", "TP (CG)", "WP", "WL (All)", "WL (CG)"], ["solver_time_ms"], ["Time (s)"])

make_table(data, ["tidal_shared", "tidal_roaring"], ["TP (Shared)", "TP (Roaring)"], ["solver_time_ms"], ["Time (s)"])

make_table(data, ["tidal_shared"], [""], ["num_called_functions", "num_called_non_trivial_functions", "mean_call_edges", "mean_non_trivial_call_edges"], ["\\# Called", "\\# Called (non-trivial)", "Mean Call Edges", "Mean Call Edges (non-trivial)"])