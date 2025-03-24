import re
from functools import reduce 
import operator
import statistics
import sys

my_nums = [];
my_cores = [2,4,6,8,10,12,14,16,18,20,22,24,26,28];

def get_data(file):
    with open(file) as f:
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

    avgs = [sum(out2[i:i+5])//5 for i in range(0,len(out2),5)]

    return(avgs)


df = get_data(file=sys.argv[1])
core = 2;
for avg in df:
    print(core, " : " , avg)
    core = core + 2;