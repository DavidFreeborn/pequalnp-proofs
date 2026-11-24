# An exhaustive semantic check of small cases, not a proof of L-meta-3064.
import time,json
n=9; mask=(1<<512)-1
variables=[sum(1<<s for s in range(512) if (s>>i)&1) for i in range(n)]
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]
target=0
for a,b in edges: target |= variables[a]&variables[b]
initial=variables+[variables[4]|variables[6],0,mask]
counts=[0,0,0,0]; found=None
start=time.time()
def visit(wires,depth):
    global found
    counts[depth]+=1
    if depth==3:return
    candidates=set()
    for a in wires:
        candidates.add(a^mask)
    for i,a in enumerate(wires):
        for b in wires[i:]:
            candidates.add(a&b);candidates.add(a|b)
    candidates.difference_update(wires)
    for value in candidates:
        if value!=mask and value&target==target:
            found={"depth":depth+1,"equals_target":value==target}
            return
        visit(wires+[value],depth+1)
        if found:return
visit(initial,0)
print(json.dumps({"gates_after_fixed_or":3,"constants_given_free":True,
"semantic_program_prefixes":counts,"nonconstant_superfunction_of_target_found":found,
"seconds":round(time.time()-start,3)}))
