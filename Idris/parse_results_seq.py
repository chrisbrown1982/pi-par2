import re
from functools import reduce 
import operator
import statistics
import sys

my_nums = [];

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

    return(statistics.mean(out2))


df = get_data(file=sys.argv[1])
print(df)