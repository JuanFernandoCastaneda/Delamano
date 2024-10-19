act = [1, 3, 2, 2, 1, 3, 1, 2, 2, 4, 1, 3, 1, 3]
print(len(act))
rew = {1:18, 2:8, 3:16, 4:12}

tot_rew = {i: 0 for i in range(1, 5)}
occ = {i: 0 for i in range(1, 5)}

for i in range(len(act)):
  if i%2 == 0:
    path = act[i]
    tot_rew[path] += rew[path]
    occ[path] += 1
  else:
    if i+1%4 == 0:
      for key in occ.keys():
        occ[key] += 0.25
    else:
      for key in occ.keys():
        tot_rew[path] += rew[path]*0.25
        occ[key] += 0.25

print(tot_rew)
print(occ)
