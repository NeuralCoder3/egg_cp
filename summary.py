import os
import re

log_dir = "logs"
# go through all _log.txt files
data = []
for filename in os.listdir(log_dir):
    if not filename.endswith("_log.txt"):
        continue
    
    with open(os.path.join(log_dir, filename), "r") as f:
        content = f.read()
    # extract the last line that contains "Final Accuracy"
    match = re.search(r"Solved (\d+)/\d+,", content)
    if not match:
        continue
    count = int(match.group(1))
        
    # Starting Caviar CP with configuration: Args { suffix: "v115", egraph_iterations: 1000, nodes: 5000, total_time: 10, iterations: 5, cp_count: 100, cp_retain: 20, continue_from: 0
    # match = re.search(r"Args { suffix: \"(v\d+)\", egraph_iterations: (\d+), nodes: (\d+), total_time: (\d+), iterations: (\d+), cp_count: (\d+), cp_retain: (\d+), continue_from: (\d+) }", content)
    # if match:
    #     suffix = match.group(1)
    #     egraph_iterations = int(match.group(2))
    #     nodes = int(match.group(3))
    #     total_time = int(match.group(4))
    #     iterations = int(match.group(5))
    #     cp_count = int(match.group(6))
    #     cp_retain = int(match.group(7))
    #     continue_from = int(match.group(8))
    #     print
    
    # get string between args
    args_match = re.search(r"Args { (.+) }", content)
    if not args_match:
        continue
    
    args_str = args_match.group(1)
    args_dict = {}
    for arg in args_str.split(", "):
        key, value = arg.split(": ")
        args_dict[key] = value.strip('"')
        
    version = filename.split("_")[0]
    # print(f"{version}: {count}/100, Args: {args_dict}")
    data.append((version, count, args_dict))
    
data = sorted(data, key=lambda x: x[0])
for version, count, args_dict in data:
    print(f"{version}: {count}/100, Args: {args_dict}")