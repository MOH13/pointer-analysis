import re
from collections import defaultdict

with open("./solved.dot") as file:
    in_degrees = defaultdict(int)
    out_degrees = defaultdict(int)
    for line in file.readlines():
        res = re.match(
            "\s*n(\d+) -> n(\d+)\\[.* style=\"solid\".*\\]", line.strip())
        if res:
            captures = res.groups()
            out_degrees[int(captures[0])] += 1
            in_degrees[int(captures[1])] += 1

    print(sorted(in_degrees.items(), key=lambda x: x[1]))
