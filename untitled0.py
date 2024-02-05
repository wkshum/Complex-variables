# -*- coding: utf-8 -*-
"""
Created on Wed Aug 30 12:30:06 2023

@author: User


"""

def bin_repr(i : int) -> str:
    """ binary repesentation of the absolute value of i """
    return(bin(abs(i))[2:])

def str_len(s: str) -> int :
    """ Return the length of a string """
    return len(s)
	
def is_even(x : int) -> bool:
    """  Checks if a number is even or odd """
    return True if x%2 ==0 else False

def compose (function1, function2):
	def function3(x):
		return (function2(function1(x)))
	return function3

f = compose(bin_repr, str_len)
g = compose(str_len, is_even)

i = 2023 
print(is_even(f(i)))
print(g(bin_repr(i)))

#%%

from numpy import random
import matplotlib.pyplot as plt

def Cantor(m=30):   # generate Cantor distributed r.v.
    return sum([3**(-n)*random.choice([0,2]) \
                for n in range(1,m)])

h = []
for _ in range(100):
    h.append(Cantor())

y = [1 for n in range(100)]
plt.scatter(h,y, s=0.5)



#%% 

from numpy import random, floor

def generate_UV():   # generate r.v. U and V
    U = random.uniform(0,2)
    V = floor(U)
    return (U,V)

u = 1.7  # u and v can be set to any real number
v = 1.6

n = 80000  # generate n samples
a = map(lambda x: x[0]<=u and  x[1]<=v, [generate_UV() for _ in range(n)])
print(f"Prob(U<={u}, V<={v}) = {sum(a)/n}")


#%%

from numpy import random
from itertools import accumulate

alphabet = ['a','b','c']
dist = [1/3, 1/3, 1/3]   # prob. mass function
n = 30   # string length
pattern = "aaa"

# cumulative distribution
cum_dist = list(accumulate( dist, lambda x,y: x+y))

random_string = ""         # empty string
for _ in range(n):
    u = random.uniform(0,1)     # generate uniform r.v.
    random_char= alphabet[sum([u > p for p in cum_dist])] 
    random_string += random_char              # append char to string

occur = [i for i in range(len(random_string)-len(pattern)+1) \
         if random_string[i:i+len(pattern)] == pattern ]

print(random_string)
if occur==[]:
    print(f"The pattern {pattern} does not occur")
else:
    print(f"The pattern {pattern} occurs at position {occur}")




#%%


random_string = "" # empty string
n=0
while True:
    u = random.uniform(0,1)  # generate uniform r.v.
    random_char= alphabet[sum([u > p for p in cum_dist])]  
    random_string += random_char # randomly draw a character
    if random_string[-len(pattern):] == pattern:
        print(random_string)
        n = n + 1
        if n == 6: break
           # break # break if we see the pattern at the end
           
#%% ball bin model


from random import randint
from numpy import exp

# throw k balls into n bins
n = 1000 # number of bins
k = 2000 # number of balls

# locations of the k balls
locations = [ randint (0,n -1) for _ in range (k)]
# compute the number of balls in each bin
occupancy = [sum ([x==i for x in locations ]) for i in range (n)]
# Find the number of bins with exactly 1 ball
X = sum ([y==0 for y in occupancy ])

print(f"Number of bins : n = {n}")
print(f"Number of balls: k = {k}")
print (f"Number of empty bins divided by the number of bins : {X/n}")
print (f"Compare with e^(-k/n) = {exp(-k/n)}")


#%%

from numpy import random
from numpy import exp

def generate_XY (_lambda):  # a coupling of Bernoulli and Poisson
    Y = random.poisson(_lambda)
    X = min(Y,1)
    if Y==0 and random.uniform() > (1-_lambda)/exp(-_lambda):
        X = 1
    return (X,Y)

_lambda = 0.75   # the common mean of Bernoulli and Poisson

# test P(X=1) = lambda
# and P(X=Y) = 1 - lambda + lambda e^(-lambda)
s = t = 0 
n = 10000   # number of samples
for _ in range(n):
    pair = generate_XY(_lambda)  # generate joint r.v. X and Y
    s += pair[0]
    t += pair[0]==pair[1]
print(f"Sample mean of X = {s/n}")
print(f"Probability that X equals Y is {t/n}")
print(f"Compare with the exact value {1 - _lambda + _lambda * exp(-_lambda)}")


#%%

from random import choice
A = ['a','b','c'] # alphabet = {a,b,c}
pattern = 'ba'

random_string = "" # initialize to empty string
while True:
    random_string += choice ( A ) 
    if random_string [-len ( pattern ):] == pattern :
        break
    
print(random_string)
#%%

from random import choice
A = ['a','b','c'] # alphabet = {a,b,c}

def monkey ( alphabet , pattern ):
    random_string = "" # initialize to empty string
    while True:
        random_string += choice ( alphabet ) # randomly draw a character
        if random_string [-len ( pattern ):] == pattern :
            break # break if we see the pattern at the end
    return len ( random_string ) # return the length of the random string

n = 1000   # run the experiment n times
waiting_time1 = sum ([ monkey (A,'abab') for _ in range (n)])/n
waiting_time2 = sum ([ monkey (A,'aabb') for _ in range (n)])/n
print (f" Average waiting time for pattern abab ={ waiting_time1 }")
print (f" Average waiting time for pattern aabb ={ waiting_time2 }")


#%%
from random import choice
Arrival = [0, 0, 0, 1, 1, 1, 1, 1, 2, 2 ] 

x0 = 6   # initial number of people in th queue

def generate_queue (x0):
    Q = [x0]
    while Q[-1]>0:   # while the queue is not empty
        Q.append(Q[-1]-1+choice(Arrival))
    return Q

# print out a sample path
print (generate_queue(x0))

# compute average by Monte Carlo 
n = 10000
S = 0
for _ in range(n):
    S += len(generate_queue(x0))-1
print(f"Average waiting time until the queue is empty = {S/n}")


#%%
# Absolute value and phase
	
from cmath import phase
from numpy import abs,sin, cos



z = -1+1j
w1 = (z**3)**(1/4) # raise to the power 3 and then take fourth root
w2 = z**(3/4)  # raise to the power 3/4
print(f"w1 = {w1}")
print(f"w2 = {w2}")

print(f"\nThey are both fourth roots of {z*z*z}.")
print(f"w1^4={w1**4}")
print(f"w2^4={w2**4}")

#%%
from numpy import exp, pi

def test_concyclic(pt0, pt1, pt2, pt3):
	z0 = complex(pt0[0],pt0[1])   # convert to complex numbers
	z1 = complex(pt1[0],pt1[1])
	z2 = complex(pt2[0],pt2[1])
	z3 = complex(pt3[0],pt3[1])
	return abs(((z0-z1)*(z2-z3)/((z0-z3)*(z2-z1))).imag)< 1e-8


