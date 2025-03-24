import re
from functools import reduce 
import operator
import statistics
import sys

my_nums_seq = [];
my_nums_par = [];
my_cores = [2,4,6,8,10,12,14,16,18,20,22,24,26,28];


def get_seq(file):
    with open(file) as f:
        lines = f.readlines() # list containing lines of file 
        columns = [] # to store column names 

        i = 1 
        for line in lines:
            line = line.strip() # remove leading/trailing whitespace 
            if line.startswith("{min,"):
                my_nums_seq.append(re.findall('\d+', line))

        out = reduce(operator.concat, my_nums_seq)

        out2 = []
        for o in out:
            out2.append(int(o))

    return(statistics.mean(out2))

def get_par(file):
    with open(file) as f:
        lines = f.readlines() # list containing lines of file 
        columns = [] # to store column names 

        i = 1 
        for line in lines:
            line = line.strip() # remove leading/trailing whitespace 
            if line.startswith("{min,"):
                my_nums_par.append(re.findall('\d+', line))

        out = reduce(operator.concat, my_nums_par)

        out2 = []
        for o in out:
            out2.append(int(o))

    avgs = [sum(out2[i:i+10])//10 for i in range(0,len(out2),10)]

    return(avgs)


seq_avg  = get_seq(sys.argv[1]) 
par_avgs = get_par(sys.argv[2])
core = 2;
print("base ,", seq_avg)
for avg in par_avgs:
    print(core, " , " , avg, ",", seq_avg/avg)
    core = core + 2;