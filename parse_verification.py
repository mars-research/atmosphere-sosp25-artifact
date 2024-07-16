import json

# parse x:
f = open('/home/xiangdc/atmosphere/time.json')
data = json.load(f)

# the result is a Python dictionary:
for mod in data["times-ms"]["smt"]["smt-run-module-times"]:
    for func in mod["function-breakdown"]:
        print(func['time']/1000)