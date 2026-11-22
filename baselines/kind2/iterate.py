import re, subprocess, time, json, sys
import os
K2=os.environ.get("KIND2", "kind2")
def run(path):
    t=time.time(); out=subprocess.run([K2,"--enable","CONTRACTCK"]+(["--z3_bin",os.environ["Z3_BIN"]] if os.environ.get("Z3_BIN") else [])+["--color","false",path],capture_output=True,text=True,timeout=300).stdout
    return out, time.time()-t
res={}
for base in ("ap_orig","sen_orig"):
    src=open(base+".lus").read(); cores=[]; total=0; runs=0
    while True:
        open("tmp.lus","w").write(src); out,dt=run("tmp.lus"); total+=dt; runs+=1
        if "proven unrealizable" not in out: break
        core=re.findall(r'Guarantee (\S+) at position', out.split("CONFLICTING CONSTRAINTS")[1].split("Checking")[0])
        inp=re.findall(r'^\s+(\w+)\s+(\S+)$', out.split("== Inputs ==")[1].split("== Outputs ==")[0], re.M)
        cores.append(dict(core=core, deadlocking_input=dict(inp)))
        # drop the guarantee that the authors later revised (the second-listed one in our pairs is arbitrary; drop both choices = remove one)
        drop=next(c for c in core if c not in ("FSM-002","FSM-005","FSM-006","FSM-009","FSM-010"))
        src=re.sub(r'\s*guarantee "'+re.escape(drop)+r'".*?;\n',"\n",src)
    res[base]=dict(cores=cores, runs=runs, seconds=round(total,2))
print(json.dumps(res,indent=1)); json.dump(res,open("kind2_results.json","w"),indent=1)
