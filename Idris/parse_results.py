import re
from functools import reduce 
import operator
import statistics

my_nums = [];

with open('skel\queens\queens12_seq.txt') as f:
    lines = f.readlines() # list containing lines of file 
    columns = [] # to store column names 

    i = 1 
    for line in lines:
        line = line.strip() # remove leading/trailing whitespace 
        if line.startswith("{min,"):
            my_nums.append(re.findall('\d+', line))

    out = reduce(operator.concat, my_nums)

    out2 = []
    for o in out:
        out2.append(int(o))

    print(statistics.mean(out2)/1000000)

